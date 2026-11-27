import json
import os
from pathlib import Path
import re
import signal
import subprocess
import tempfile
import time

from .source import IDENT


class CheckError(Exception):
    pass


def command(args, cwd, timeout, log, *, env=None):
    """Bound the full process group, including any Lean children launched by Lake."""
    with log.open('wb') as output:
        p = subprocess.Popen(args, cwd=cwd, env=env, stdout=output,
                             stderr=subprocess.STDOUT, start_new_session=True)
        try:
            code = p.wait(timeout=timeout)
        except (subprocess.TimeoutExpired, KeyboardInterrupt) as exc:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            p.wait()
            if isinstance(exc, KeyboardInterrupt):
                raise
            raise CheckError(f'timed out after {timeout}s running {args!r}') from exc
    if code:
        with log.open('rb') as f:
            f.seek(max(0, log.stat().st_size-3000))
            tail = f.read().decode(errors='replace')
        raise CheckError(f'exit {code} running {args!r}\n{tail}')
    return log


def safe_path(root, name):
    rel = Path(name)
    path = (root/rel).resolve()
    if rel.is_absolute() or '..' in rel.parts or not path.is_relative_to(root.resolve()):
        raise ValueError(f'path outside checkout: {name}')
    return path


def read_spec(path):
    spec = json.loads(path.read_text())
    if not spec.get('endpoints') or not re.fullmatch(IDENT,spec['entry']):
        raise ValueError('a module and at least one reference theorem type are required')
    scopes = spec.get('open_scoped', [])
    if not isinstance(scopes, list) or any(
        not isinstance(scope, str) or not re.fullmatch(IDENT, scope) for scope in scopes
    ):
        raise ValueError('open_scoped must contain Lean scope names')
    for name, ty in spec['endpoints'].items():
        if not re.fullmatch(IDENT, name) or not isinstance(ty, str) or not ty.strip() or '\n' in ty:
            raise ValueError('invalid endpoint or reference type')
    return spec


def git(repo, *args):
    return subprocess.check_output(['git','-C',str(repo),*map(str,args)], text=True).strip()


def check_axioms(output, names, allowed):
    matches = {}
    for line in output.splitlines():
        match = re.fullmatch(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", line.strip())
        if match and match[1] in names:
            if match[1] in matches:
                raise CheckError(f'duplicate axiom report for {match[1]}')
            axioms = sorted(s.strip() for s in (match[2] or '').split(',') if s.strip())
            if set(axioms) - set(allowed):
                raise CheckError(f'unexpected axioms for {match[1]}: {axioms}')
            matches[match[1]] = axioms
    if matches.keys() != names.keys():
        raise CheckError('missing endpoint axiom output')
    return matches


class Checker:
    def __init__(self, root, spec, logs, timeout):
        self.root, self.spec, self.logs = root, spec, logs
        self.timeout = timeout
        self.env = os.environ.copy()
        self.env.pop('OPENAI_API_KEY', None)
        self.env.pop('LEAN_PATH', None)
        self.env.pop('LEAN_SRC_PATH', None)
        self.count = 0
        self.checks = []
        required = spec.get('toolchain')
        if required and (root/'lean-toolchain').read_text().strip() != required:
            raise ValueError('toolchain file differs from the case specification')

    def run(self, args):
        self.count += 1
        log = self.logs / f'{self.count:04d}-{args[-1].split("/")[-1]}.log'
        start = time.monotonic()
        path = command(args, self.root, self.timeout, log, env=self.env)
        self.checks.append({'command': args, 'seconds': round(time.monotonic()-start, 2)})
        return path

    def audit(self, modules=(), *, comparator=False):
        self.run(['lake', 'build'])
        # The Lake project may omit the public module from its default targets.
        self.run(['lake', 'build', '+' + self.spec['entry']])
        lines = ['import ' + self.spec['entry']]
        lines.extend('open scoped ' + scope for scope in self.spec.get('open_scoped', []))
        for name, ty in self.spec['endpoints'].items():
            lines.extend([f'example : {ty} := @{name}', f'#print axioms {name}'])
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', prefix='LeanReducerAudit',
                                         dir=self.root, encoding='utf-8') as probe:
            probe.write('\n'.join(lines) + '\n')
            probe.flush()
            log = self.run(['lake','env','lean',Path(probe.name).name])
            axioms = check_axioms(log.read_text(), self.spec['endpoints'], self.spec['axioms'])
        for module in dict.fromkeys([*modules, self.spec['entry']]):
            self.run(['lake', 'env', 'leanchecker', module])
        if comparator:
            self.run(['lake','comparator','--paranoid'])
        return axioms
