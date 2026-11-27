import unittest
from leanreducer.inlining import straight_line


class InlineTest(unittest.TestCase):
    def test_long_identifier_before_unsupported_operator(self):
        self.assertIsNone(straight_line(["have x := h", "exact " + "a" * 250 + " + x"]))

    def test_chained_equalities(self):
        self.assertEqual(straight_line(["  have same : Nat.succ a = Nat.succ b := h",
                                        "  have result : a = b := Nat.succ.inj same",
                                        "  exact result"]), "exact Nat.succ.inj h")

    def test_shared_value_and_binders_preserved(self):
        for lines in (["have x := expensive h", "exact pair x x"],
                      ["have x := a", "exact fun x => x"], ["have x := a", "exact h.x"]):
            self.assertIsNone(straight_line(lines))

    def test_application_parentheses(self):
        self.assertEqual(straight_line(["have v := f x", "exact g v"]), "exact g (f x)")
