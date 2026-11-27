from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from leanreducer import agents
from leanreducer.source import Corpus, bodies, imports, metrics
from leanreducer.verify import CheckError, check_axioms


class SourceAndContracts(unittest.TestCase):
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
            (root/'B.lean').write_text('import Misspelled.Helper')
            with self.assertRaises(ValueError):
                Corpus(root,['Init'])

    def test_lookalikes_and_body_boundary(self):
        src='theorem a : True := by\n  have h : True := True.intro\n  exact h\n\n/-- next -/\ntheorem b : True := True.intro\n'
        body,=bodies('A',src)
        self.assertEqual((body.start, body.stop, body.lines),(1,3,2))
        self.assertFalse(list(bodies('A','theorem x : True := by\n  trivial\n')))

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
