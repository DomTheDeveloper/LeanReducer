"""Inline singly used names in straight-line tactic proofs with applicative terms."""
import re
from .source import IDENT as NAME

TERM = re.compile(r"(?:" + NAME + r"|[() ]|\d+)+")
LOCAL = re.compile(r"have\s+([^\W\d]\w*)\s*(?::\s*.*?)?\s*:=\s*(.+)")
BINDING = {"fun", "let", "have", "by", "match", "do", "where", "forall", "show", "from"}


def straight_line(lines):
    rows = [s.strip() for s in lines if s.strip()]
    if any(len(row) > 500 for row in rows):
        return None
    if len(rows) < 2 or not rows[-1].startswith("exact "):
        return None
    term = rows[-1][6:].strip()
    bindings = [LOCAL.fullmatch(s) for s in rows[:-1]]
    if not all(bindings) or not TERM.fullmatch(term):
        return None
    if len({b[1] for b in bindings}) != len(bindings):
        return None
    for b in reversed(bindings):
        name, value = b.groups()
        if not TERM.fullmatch(value) or BINDING.intersection(re.findall(NAME, value + " " + term)):
            return None
        names = re.compile(NAME)
        if [m[0] for m in names.finditer(term)].count(name) != 1:
            return None
        replacement = value if re.fullmatch(NAME, value) or term == name else "(" + value + ")"
        term = names.sub(lambda m: replacement if m[0] == name else m[0], term)
    return "exact " + term if len(term) <= 100 else None
