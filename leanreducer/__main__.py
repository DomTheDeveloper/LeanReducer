"""Run with python -m leanreducer from the repository root."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from . import agents
from .cuts import combination_audit, joint_cut, pair_audit
from .inlining import straight_line
from .planning import replacement_plan
from .patches import apply_reviewed
from .patterns import import_audit, repeated_commands
from .source import Corpus, bodies, metrics
from .verify import CheckError, Checker, git, read_spec, safe_path


def save(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')


def build_options(corpus, closure, protected, excluded, args):
    options = []
    for module in sorted(closure):
        path = corpus.paths[module]
        if path in protected or (args.module and args.module != module):
            continue
        for body in bodies(module, path.read_text()):
            if (module, body.name, body.header) in excluded or (args.decl and body.name != args.decl):
                continue
            options.append(body)
    return sorted(options, key=lambda b: (-b.lines,b.module,b.start))


def trial(checker, corpus, body, tactics, max_trials, changes, history):
    path = corpus.paths[body.module]
    original = path.read_bytes()
    raw = original.decode().splitlines(keepends=True)
    before = corpus.sizes[body.module]
    newline = '\r\n' if raw[body.start].endswith('\r\n') else '\n'
    first = next(line for line in raw[body.start:body.stop] if line.strip())
    indent = first[:len(first)-len(first.lstrip())]
    for tactic in tactics[:max_trials]:
        edited = ''.join([*raw[:body.start], indent + tactic + newline, *raw[body.stop:]])
        after = metrics(edited)
        if after['code'] >= before['code'] or after['code_chars'] >= before['code_chars']:
            continue
        path.write_bytes(edited.encode())
        accepted = False
        try:
            checker.run(['lake','build','+' + body.module])
            axioms = checker.audit([body.module])
            history.append({'target': body.label, 'tactic': tactic, 'accepted': True,
                            'saved_lines': before['code']-after['code'], 'axioms': axioms})
            corpus.sizes[body.module] = after
            changes.add(body.module)
            accepted = True
            return
        except CheckError as exc:
            history.append({'target': body.label, 'tactic': tactic, 'accepted': False,
                            'reason': str(exc).splitlines()[0]})
        finally:
            if not accepted:
                path.write_bytes(original)


def run(args):
    spec = read_spec(args.config)
    repo = args.repo.resolve()
    rev = git(repo,'rev-parse','--verify','HEAD')
    if spec.get('revision') and spec['revision'] != rev:
        raise ValueError('checked-out HEAD differs from the pinned case revision')
    if args.ai and not os.environ.get('OPENAI_API_KEY'):
        raise ValueError('AI mode requires OPENAI_API_KEY')
    if args.output.exists():
        raise ValueError('choose a new output directory')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    timeout = args.timeout if args.timeout is not None else spec.get('timeout_seconds', 18000)
    if not isinstance(timeout, int) or args.rounds < 1 or args.trials < 1 or timeout < 1 or args.target < 0:
        raise ValueError('use positive resource limits and a nonnegative target')
    with tempfile.TemporaryDirectory(prefix='leanreducer-') as work:
        tmp = Path(work)
        checkout = tmp/'checkout'
        # Only committed source is authoritative. No inherited .lake build results.
        subprocess.run(['git','clone','--quiet','--shared','--no-checkout','--',str(repo),str(checkout)], check=True)
        git(checkout,'checkout','--quiet','--detach',rev)
        project = safe_path(checkout,spec['project'])
        src = safe_path(project,spec['source'])
        if git(checkout, 'ls-files', '--', ':(glob)**/.lake/**', ':(glob)**/*.olean'):
            raise ValueError('tracked build output would compromise a clean rebuild')
        corpus = Corpus(src, spec['boundary'])
        closure = corpus.walk(spec['entry'])
        before = corpus.size(closure)
        tree_before = corpus.size(corpus.paths)
        logs = tmp/'logs'
        logs.mkdir()
        checker = Checker(project, spec, logs, timeout)
        if args.cache:
            checker.run(['lake','exe','cache','get'])
        version_lines = checker.run(['lake','env','lean','--version']).read_text().splitlines()
        version = next((line for line in version_lines if line.startswith('Lean (version ')), '')
        if spec.get('lean_version') and not version.startswith('Lean (version ' + spec['lean_version'] + ','):
            raise ValueError('running Lean version differs from the case specification')
        axioms = checker.audit()
        protected = {safe_path(project,n) for n in spec.get('protected',[])}
        history, excluded, changes = [], set(), set()
        if args.patch:
            changed = apply_reviewed(args.patch, checkout, project, spec)
            candidate = Corpus(src, spec['boundary'])
            candidate_closure = candidate.walk(spec['entry'])
            if (candidate.size(candidate_closure)['code'] >= before['code'] or
                    candidate.size(candidate_closure)['code_chars'] >= before['code_chars'] or
                    candidate.size(candidate.paths)['code'] > corpus.size(corpus.paths)['code']):
                raise ValueError('patch must shrink the entry closure without growing the source tree')
            changes.update(changed)
        for _ in range(0 if args.patch else args.rounds):
            if corpus.size(closure)['code'] <= args.target:
                break
            options = build_options(corpus, closure, protected, excluded, args)
            if not options:
                break
            body = agents.choose(options[:32], args.ai) if args.ai else options[0]
            excluded.add((body.module, body.name, body.header))
            text = corpus.paths[body.module].read_text().splitlines(True)
            if args.ai:
                tactics = agents.suggestions((body.header + ''.join(text[body.start:body.stop]))[:24000], args.ai)
            else:
                tactics = list(dict.fromkeys(args.tactic or agents.BASIC))
                if not args.tactic:
                    direct = straight_line(text[body.start:body.stop])
                    if direct:
                        tactics.insert(0, direct)
            trial(checker,corpus,body,tactics,args.trials,changes,history)
        # Rebuild even after rejected trials and check the exact emitted tree.
        final = Corpus(src, spec['boundary'])
        axioms = checker.audit(sorted(changes & final.paths.keys()), comparator=args.paranoid)
        after = final.size(final.walk(spec['entry']))
        diff = subprocess.check_output(['git','-C',str(checkout),'diff','--no-ext-diff','HEAD','--',str(src)])
        record = {'revision': rev, 'toolchain': version, 'entry': spec['entry'],
                  'before': before, 'after': after, 'tree_before': tree_before, 'tree_after': final.size(final.paths),
                  'target': args.target,
                  'target_met': after['code'] <= args.target, 'axioms': axioms,
                  'paranoid_comparator': args.paranoid, 'changes': sorted(changes),
                  'removed_modules': sorted(changes - final.paths.keys()),
                  'mode': 'reviewed patch' if args.patch else ('AI' if args.ai else 'offline'),
                  'attempts': history, 'checks': checker.checks,
                  'patch_sha256': hashlib.sha256(diff).hexdigest()}
        # Publish both deliverables together, only after a successful final audit.
        with tempfile.TemporaryDirectory(prefix='.leanreducer-',dir=args.output.parent) as temp:
            result = Path(temp)/'result'
            result.mkdir()
            (result/'reduction.patch').write_bytes(diff)
            save(result/'verification.json',record)
            if args.output.exists():
                raise ValueError('output directory was created by another process')
            result.rename(args.output)
        print(json.dumps({k:record[k] for k in ('before','after','target','target_met','changes')},indent=2))


def main():
    parser = argparse.ArgumentParser(description='Measure and shorten Lean proof source.')
    commands = parser.add_subparsers(dest='command',required=True)
    analysis = commands.add_parser('analyze', help='count source and local import closures')
    analysis.add_argument('source',type=Path)
    analysis.add_argument('--entry',required=True)
    analysis.add_argument('--external',action='append',default=['Init','Std','Lean','Mathlib'])
    analysis.add_argument('--import-audit', action='store_true', help='report redundant direct module imports')
    analysis.add_argument('--repetitions', action='store_true', help='find repeated seal/unseal commands and shared imports')
    analysis.add_argument('--cut',action='append',default=[])
    analysis.add_argument('--pair-audit', action='store_true',
                          help='measure all pairs of module cuts below the entry')
    analysis.add_argument('--triple-audit', action='store_true',
                          help='measure all triples of module cuts below the entry')
    analysis.add_argument('--exclude-from-pairs', '--exclude-from-audit', metavar='MODULE',
                          action='append', default=[], help='omit this module as a candidate in the audit')
    analysis.add_argument('--plan-cut', metavar='MODEL',
                          help='ask the architecture agent for an unverified mathematical replacement of one cut')
    analysis.add_argument('--target',type=int,default=50000)
    analysis.add_argument('--json',type=Path)
    reduce = commands.add_parser('reduce', help='try shorter proof bodies in an isolated checkout')
    reduce.add_argument('--repo',required=True,type=Path)
    reduce.add_argument('--config',required=True,type=Path)
    reduce.add_argument('--output',required=True,type=Path)
    reduce.add_argument('--target',type=int,default=50000)
    reduce.add_argument('--rounds',type=int,default=1)
    reduce.add_argument('--trials',type=int,default=6)
    reduce.add_argument('--timeout',type=int,help='seconds per build or check, defaults to the case timeout or 18000')
    reduce.add_argument('--cache',action='store_true',help='download the pinned Mathlib cache in the clean checkout')
    reduce.add_argument('--paranoid',action='store_true',help='also require Lake Comparator in the final audit')
    reduce.add_argument('--module')
    reduce.add_argument('--decl')
    mode = reduce.add_mutually_exclusive_group()
    mode.add_argument('--patch', type=Path, help='verify a reviewed multi-module source diff against the frozen Comparator challenge')
    mode.add_argument('--ai',metavar='MODEL',help='run the planner, prover and reviewer over the Responses API')
    mode.add_argument('--tactic',choices=agents.BASIC,action='append',help='offline tactics, in attempt order')
    args = parser.parse_args()
    if args.command == 'analyze':
        corpus = Corpus(args.source.resolve(),args.external)
        report = corpus.report(args.entry,args.cut)
        if len(set(args.cut)) > 1:
            report['joint_cut'] = joint_cut(corpus, args.entry, args.cut)
        if args.exclude_from_pairs and not (args.pair_audit or args.triple_audit):
            raise ValueError('cut exclusions require --pair-audit or --triple-audit')
        if args.pair_audit:
            report['pair_audit'] = pair_audit(corpus, args.entry, args.target, args.exclude_from_pairs)
        if args.triple_audit:
            report['triple_audit'] = combination_audit(
                corpus, args.entry, args.target, args.exclude_from_pairs, size=3)
        if args.plan_cut:
            if len(args.cut) != 1:
                raise ValueError('--plan-cut requires exactly one --cut')
            cut = args.cut[0]
            report['replacement_plan'] = replacement_plan(
                corpus, args.entry, cut, report['cuts'][cut], args.target, args.plan_cut)
        if args.import_audit:
            report['import_audit'] = import_audit(corpus, args.entry)
        if args.repetitions:
            report['repeated_commands'] = repeated_commands(corpus, args.entry)
        report['target'] = args.target
        report['gap'] = max(0,report['closure']['code']-args.target)
        if args.json:
            save(args.json,report)
        print(json.dumps(report,ensure_ascii=False,indent=2))
    else:
        run(args)


if __name__ == '__main__':
    try:
        main()
    except (CheckError, ValueError, KeyError, OSError, subprocess.CalledProcessError) as exc:
        sys.exit(str(exc))
