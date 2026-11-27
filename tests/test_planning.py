from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from leanreducer.cuts import joint_cut
from leanreducer.planning import excerpt, replacement_plan
from leanreducer.source import Corpus


class ReplacementPlanTest(unittest.TestCase):
    def test_shared_prerequisite_is_charged_once(self):
        with TemporaryDirectory() as temp:
            root = Path(temp)
            for name, source in {"Main": "import A B", "A": "import Shared",
                                 "B": "import Shared", "Shared": "theorem p : True := trivial"}.items():
                (root / (name + ".lean")).write_text(source + "\n")
            corpus = Corpus(root, [])
            cut = corpus.report("Main", ["A"])["cuts"]["A"]

            def fake_request(role, model, payload):
                self.assertEqual(role, "architect")
                self.assertEqual(payload["replacement_budget"], 2)
                self.assertEqual(payload["exclusive_code_lines"], 1)
                self.assertEqual(payload["caller_modules"], ["Main"])
                self.assertTrue(payload["cut_source"]["complete"])
                return {"replacement_statement": "Use p.", "first_lean_check": "Check p.",
                        "proof_obligations": ["Derive the caller's result."], "dependencies_to_check": ["p"]}

            result = replacement_plan(corpus, "Main", "A", cut, 5, "fixture", request=fake_request)
            self.assertEqual(result["status"], "unverified research proposal")

    def test_unreachable_module_rejected_before_api_call(self):
        with TemporaryDirectory() as temp:
            root = Path(temp)
            for name in ["Main", "Unused"]:
                (root / (name + ".lean")).write_text("theorem example" + name + " : True := trivial\n")
            corpus = Corpus(root, [])
            with self.assertRaisesRegex(ValueError, "outside the import closure"):
                replacement_plan(corpus, "Main", "Unused", {}, 10, "fixture", request=self.fail)

    def test_joint_plan_charges_shared_dependency_once_and_tracks_callers(self):
        with TemporaryDirectory() as temp:
            root = Path(temp)
            for name, source in {"Main": "import A B", "A": "import Shared", "B": "import Shared",
                                 "Shared": "theorem p : True := trivial"}.items():
                (root / (name + ".lean")).write_text(source + "\n")
            corpus = Corpus(root, [])
            counts = joint_cut(corpus, "Main", ["A", "B"])

            def request(role, model, payload):
                self.assertEqual(payload["cuts"], ["A", "B"])
                self.assertEqual(payload["imports_by_caller"], {"Main": ["A", "B"]})
                self.assertEqual(payload["exclusive_code_lines"], 3)
                self.assertEqual(payload["code_released_by_no_single_cut"], 1)
                self.assertEqual(payload["replacement_budget"], 2)
                self.assertEqual(set(payload["cut_sources"]), {"A", "B"})
                return {"replacement_statement": "Prove the caller directly.", "first_lean_check": "Test p.",
                        "proof_obligations": ["Derive p."], "dependencies_to_check": []}

            result = replacement_plan(corpus, "Main", ["B", "A", "A"], counts, 3, "fixture", request=request)
            self.assertEqual(result["cuts"], ["A", "B"])
            self.assertEqual(excerpt(root / "Main.lean", 0), {"complete": False, "start": "", "end": ""})
