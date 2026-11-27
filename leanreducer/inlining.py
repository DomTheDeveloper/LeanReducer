"""Inline singly used names in straight-line tactic proofs with applicative terms."""
import re
from .source import IDENT

NAMES = re.compile(IDENT)
TOKENS = re.compile(IDENT + r"|[0-9]+|[() ]+")
LOCAL = re.compile(r"have\s+([^\W\d]\w*)\s*(?::\s*.*?)?\s*:=\s*(.+)")
BINDING = {"fun", "let", "have", "by", "match", "do", "where", "forall", "show", "from"}


def simple_term(term):
    end = 0
    for token in TOKENS.finditer(term):
        if token.start() != end:
            return False
        end = token.end()
    return end > 0 and end == len(term)


def straight_line(lines):
    rows = [s.strip() for s in lines if s.strip()]
    if any(len(row) > 500 for row in rows):
        return None
    if len(rows) < 2 or not rows[-1].startswith("exact "):
        return None
    term = rows[-1][6:].strip()
    bindings = [LOCAL.fullmatch(s) for s in rows[:-1]]
    if not all(bindings) or not simple_term(term):
        return None
    if len({b[1] for b in bindings}) != len(bindings):
        return None
    for binding in reversed(bindings):
        name, value = binding.groups()
        if not simple_term(value) or BINDING.intersection(NAMES.findall(value + " " + term)):
            return None
        if NAMES.findall(term).count(name) != 1:
            return None
        replacement = value if NAMES.fullmatch(value) or term == name else "(" + value + ")"
        term = NAMES.sub(lambda m: replacement if m[0] == name else m[0], term)
    return "exact " + term if len(term) <= 100 else None
