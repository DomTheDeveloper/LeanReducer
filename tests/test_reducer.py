import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from leanreducer import agents
from leanreducer.patterns import import_audit, repeated_commands
from leanreducer.source import Corpus, bodies, imports, metrics
from leanreducer.verify import CheckError, check_axioms, read_spec


class SourceAndContracts(unittest.TestCase):
    def test_reference_statement_scopes(self):
        with TemporaryDirectory() as temp:
            case = Path(temp) / 'case.json'
            spec = {'entry': 'Main', 'endpoints': {'publicResult': 'True'}}
            for scopes in [[], ['Classical'], ['CategoryTheory.MonoidalCategory']]:
                case.write_text(json.dumps({**spec, 'open_scoped': scopes}))
                self.assertEqual(read_spec(case)['open_scoped'], scopes)
            for invalid in ['Classical', ['Classical\nsection'], [None]]:
                case.write_text(json.dumps({**spec, 'open_scoped': invalid}))
                with self.assertRaisesRegex(ValueError, 'scope names'):
                    read_spec(case)

    def test_lean_literals_and_nested_comments(self):
        source = '/- outer /- inner -/\n-/ import Init\ndef a := "--"\ndef b := r##"/-hi-/"##\n-- end'
        self.assertEqual((metrics(source)['physical'], metrics(source)['code']),(5,3))
        self.assertEqual(imports(source),['Init'])
        self.assertEqual(imports('module\npublic meta import Lean\nimport Std\n'),['Lean','Std'])

    def test_diamond_counts_shared_module_once(self):
        with TemporaryDirectory() as tmp:
            root=Path(tmp)
            for name, code in {'Main':'import L\nimport R','L':'import B','R':'import B','B':'import Init'}.items():
                (root/(name+'.lean')).write_text(code)
            corpus=Corpus(root,['Init'])
            report=corpus.report('Main',['L'])
            self.assertEqual(report['closure']['code'],5)
            self.assertEqual(report['cuts']['L']['exclusive_to_cut']['modules'],1)
            self.assertEqual(import_audit(corpus, 'Main')['redundant'], [])
            (root/'Main.lean').write_text('import L\nimport R\nimport B')
            checked = import_audit(Corpus(root, ['Init']), 'Main')
            self.assertEqual(checked['redundant'], [{'module': 'Main', 'import': 'B', 'also_via': ['L', 'R']}])
            (root/'B.lean').write_text('import Misspelled.Helper')
            with self.assertRaises(ValueError):
                Corpus(root,['Init'])

    def test_lookalikes_and_body_boundary(self):
        src='theorem a : True := by\n  have h : True := True.intro\n  exact h\n\n/-- next -/\ntheorem b : True := True.intro\n'
        body,=bodies('A',src)
        self.assertEqual((body.start, body.stop, body.lines),(1,3,2))
        self.assertFalse(list(bodies('A','theorem x : True := by\n  trivial\n')))

    def test_import_audit_reports_a_cycle(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root/'A.lean').write_text('import B')
            (root/'B.lean').write_text('import A')
            with self.assertRaisesRegex(ValueError, 'cyclic Lean imports'):
                import_audit(Corpus(root, []), 'A')

    def test_repeated_command_scope_and_host(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            files = {'Main': 'import A\nimport B', 'A': 'import C\nseal X.a\n  X.b',
                     'B': 'import C\nseal X.a\n  X.b in\nexample : True := trivial', 'C': 'import Init'}
            for mod, src in files.items():
                (root / (mod + '.lean')).write_text(src)
            group, = repeated_commands(Corpus(root, ['Init']), 'Main')
            self.assertEqual(group['common_modules'], ['C'])
            self.assertEqual(group['gross_call_site_lines_saved'], 2)
            self.assertEqual([s['scoped'] for s in group['sites']], [False, True])

    def test_nested_default_is_not_a_theorem_body(self):
        source = ('theorem withDefault (h : True := by\n  trivial\n  done) : True := by\n  exact h\n')
        self.assertEqual(list(bodies('A', source)), [])

    def test_axioms_fail_closed(self):
        names={'x':'True','y':'True'}
        ok="'x' does not depend on any axioms\n'y' depends on axioms: [propext]"
        self.assertEqual(check_axioms(ok,names,['propext']),{'x':[],'y':['propext']})
        for wrong in [ok.replace('propext','sorryAx'),ok.splitlines()[0],ok+'\n'+ok.splitlines()[0]]:
            with self.assertRaises(CheckError):
                check_axioms(wrong,names,['propext'])

    def test_ranked_model_proposals(self):
        responses={'prover':{'proposals':[{'tactic':'simp','lemmas':[]},{'tactic':'exact','lemmas':['Nat.add_zero']}]},
                   'reviewer':{'order':[1,0]}}
        self.assertEqual(agents.suggestions('example','test',request=lambda role,*_:responses[role]),
                         ['exact Nat.add_zero','simp'])
        for bad in ['Nat.add_zero\n  sorry','by exact True.intro','x; done']:
            with self.assertRaises(ValueError):
                agents.render({'tactic':'exact','lemmas':[bad]})
        def transport(body):
            self.assertFalse(body['store'])
            return {'status':'completed','output':[{'type':'message','content':[{'type':'output_text','text':'{"id":0}'}]}]}
        self.assertEqual(agents.ask('planner','test',{},transport=transport),{'id':0})
