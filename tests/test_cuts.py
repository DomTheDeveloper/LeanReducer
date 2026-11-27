from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from leanreducer.cuts import joint_cut, pair_audit
from leanreducer.source import Corpus


class CutTest(unittest.TestCase):
    def setUp(self):
        temp = TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        graph = {"Main": ["A", "B", "C"], "A": ["X", "Y"], "B": ["Y", "Z"],
                 "C": ["Z"], "X": ["Base"], "Y": ["Base"], "Z": ["Base"],
                 "Base": [], "Unused": []}
        for i, (name, deps) in enumerate(graph.items()):
            lines = ["import " + " ".join(deps)] if deps else []
            lines.extend(f"def value{name}{j} := {j}" for j in range(i + 1))
            (root / f"{name}.lean").write_text("\n".join(lines) + "\n")
        self.corpus = Corpus(root, [])

    def test_pair_counts_match_independent_traversals(self):
        c = self.corpus
        for excluded in [[], ["B"], ["X", "Y", "Z"], ["Main"]]:
            eligible = sorted(c.walk("Main") - {"Main", *excluded})
            brute = sorted((c.size(c.walk("Main", pair))["code"], pair)
                          for pair in combinations(eligible, 2))
            for target in range(0, 65, 4):
                report = pair_audit(c, "Main", target, excluded)
                self.assertEqual(report["pairs_examined"], len(brute))
                self.assertEqual(report["pairs_meeting_target_before_replacement"],
                                 sum(lines <= target for lines, _ in brute))
                best = report["best_pair"]
                self.assertEqual(best["modules"], list(brute[0][1]))
                self.assertEqual(best["remaining_before_replacement"]["code"], brute[0][0])

    def test_counts_shared_dependencies_once(self):
        c = self.corpus
        report = joint_cut(c, "Main", ["A", "B", "A"])
        self.assertEqual(report["released_by_no_single_cut"], c.size({"Y"}))
        self.assertEqual(report["requiring_every_cut"], c.size({"Y"}))
        self.assertEqual(report["exclusive_to_joint_cut"], c.size({"A", "B", "X", "Y"}))
        triple = joint_cut(c, "Main", ["A", "B", "C"])
        self.assertEqual(triple["released_by_no_single_cut"], c.size({"Base", "Y", "Z"}))
        self.assertEqual(triple["requiring_every_cut"], c.size({"Base"}))
        with self.assertRaisesRegex(ValueError, "reachable"):
            pair_audit(c, "Main", 50, ["Unused"])
        no_pairs = pair_audit(c, "Base", 0)
        self.assertEqual(no_pairs["pairs_examined"], 0)
        self.assertIsNone(no_pairs["best_pair"])
