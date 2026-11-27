from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from leanreducer.planning import replacement_plan
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
