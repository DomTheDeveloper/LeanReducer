"""Census of project-owned Lean source and restricted proof-body locations."""
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
import re

IDENT = r"[^\W\d][\w'₀-₉]*(?:\.[^\W\d][\w'₀-₉]*)*"
HEADER = re.compile(r"^\s*(?:(?:public|private|meta|all)\s+)*import\s+(.+)$")
DECL = re.compile(r"^(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+(" + IDENT + r")(?=\s|[:({\[])")
RAW = re.compile(r'r(#{0,32})"')
CHAR = re.compile(r"'(?:[^'\\\n]|\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.))'")


def lexical_lines(source):
    """Yield (code, structural text). Literals contribute to code but never to header detection."""
    depth = 0
    closer = None
    escaped = False
    for line in source.split('\n'):
        code, structure = [], []
        i = 0
        while i < len(line):
            if depth:
                if line.startswith('/-', i):
                    depth += 1
                    i += 2
                elif line.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            elif closer is not None:
                if not escaped and line.startswith(closer, i):
                    code.append(closer)
                    i += len(closer)
                    closer = None
                else:
                    c = line[i]
                    code.append(c)
                    escaped = (closer == '"' and c == '\\' and not escaped)
                    i += 1
            elif line.startswith('--', i):
                break
            elif line.startswith('/-', i):
                code.append(' ')
                structure.append(' ')
                depth = 1
                i += 2
            else:
                c = line[i]
                raw = RAW.match(line, i) if c == 'r' and (i == 0 or not line[i-1].isalnum()) else None
                char = CHAR.match(line, i) if c == "'" and (i == 0 or not (line[i-1].isalnum() or line[i-1] == '_')) else None
                if raw or char:
                    match = raw or char
                    code.append(match[0])
                    structure.append('§')
                    i = match.end()
                    if raw:
                        closer = '"' + raw[1]
                        escaped = False
                else:
                    code.append(c)
                    if c in '"«':
                        closer = '"' if c == '"' else '»'
                        escaped = False
                        structure.append('§')
                    else:
                        structure.append(c)
                    i += 1
        yield ''.join(code), ''.join(structure)
        escaped = False
    if depth or closer:
        raise ValueError('unterminated Lean literal or block comment')


def metrics(source):
    code = [line for line, _ in lexical_lines(source) if line.strip()]
    return {'physical': source.count('\n') + int(bool(source) and not source.endswith('\n')),
            'code': len(code), 'code_chars': sum(len(''.join(x.split())) for x in code),
            'bytes': len(source.encode())}


def imports(source):
    """Read ordinary Lake module headers. Fail explicitly on unsupported header syntax."""
    result = []
    started = False
    ended = False
    for _, structural in lexical_lines(source):
        s = structural.strip()
        if not s:
            continue
        match = HEADER.fullmatch(s)
        if match:
            if ended:
                raise ValueError('import after the header or unsupported multiline import')
            for name in match[1].split():
                if not re.fullmatch(IDENT, name):
                    raise ValueError(f'unsupported import name {name!r}')
                result.append(name)
            started = True
        elif s in ('prelude', 'module') and not started and not ended:
            continue
        elif s.endswith('import') and re.fullmatch(r'(?:(?:public|private|meta|all)\s+)*import', s):
            raise ValueError('multiline import header is unsupported')
        elif started and not ended and structural[0].isspace() and re.fullmatch(IDENT,s):
            raise ValueError(f'ambiguous import continuation {s!r}')
        else:
            ended = True
            # Imports embedded in later syntax quotations are not module imports.
            break
    return result


class Corpus:
    def __init__(self, root, boundary):
        self.root = Path(root)
        if not self.root.is_dir():
            raise ValueError(f'no source root: {self.root}')
        self.paths = {'.'.join(p.relative_to(root).with_suffix('').parts): p
                      for p in sorted(self.root.rglob('*.lean')) if '.lake' not in p.relative_to(root).parts}
        if not self.paths:
            raise ValueError('empty Lean source tree')
        self.sizes, self.deps, self.external = {}, {}, set()
        for name, path in self.paths.items():
            if path.is_symlink() or not path.resolve().is_relative_to(self.root.resolve()):
                raise ValueError(f'symlinked source module: {path}')
            text = path.read_bytes().decode('utf-8')
            self.sizes[name] = metrics(text)
            self.deps[name] = []
            for dep in imports(text):
                if dep in self.paths:
                    self.deps[name].append(dep)
                elif not any(dep == prefix or dep.startswith(prefix + '.') for prefix in boundary):
                    raise ValueError(f'{name} imports {dep}; supply its source or declare an external boundary')
                else:
                    self.external.add(dep)

    def walk(self, entry, cut=()):
        if entry not in self.paths or set(cut) - self.paths.keys():
            raise ValueError('unknown entry or cut module')
        seen, todo = set(), [entry]
        while todo:
            name = todo.pop()
            if name not in seen and name not in cut:
                seen.add(name)
                todo.extend(self.deps[name])
        return seen

    def size(self, names):
        total = Counter()
        for name in names:
            total.update(self.sizes[name])
        return {'modules': len(names), **{k: total[k] for k in ('physical', 'code', 'code_chars', 'bytes')}}

    def report(self, entry, cuts=()):
        closure = self.walk(entry)
        groups = sorted({name.partition('.')[0] for name in closure})
        rows = {}
        for cut in cuts:
            kept = self.walk(entry, (cut,))
            rows[cut] = {'own_closure': self.size(self.walk(cut)),
                         'exclusive_to_cut': self.size(closure - kept),
                         'remaining_before_replacement': self.size(kept)}
        return {'entry': entry, 'tree': self.size(self.paths), 'closure': self.size(closure),
                'groups': {g: self.size([n for n in closure if n.partition('.')[0] == g]) for g in groups},
                'external_imports': sorted(self.external), 'cuts': rows}


@dataclass(frozen=True)
class Body:
    module: str
    name: str
    start: int
    stop: int
    header: str
    lines: int

    @property
    def label(self):
        return f'{self.module}:{self.name}@{self.start + 1}'


def bodies(module, source):
    """Only select top-level declarations ending their header in := by, with an indented body."""
    raw = source.splitlines(keepends=True)
    lex = list(lexical_lines(source))[:len(raw)]
    starts = [i for i, (_, s) in enumerate(lex) if s.strip() and not s[0].isspace()]
    for k, i in enumerate(starts):
        match = DECL.match(lex[i][1])
        if not match:
            continue
        end = starts[k+1] if k+1 < len(starts) else len(raw)
        # This recognizer accepts a simple header only. An assignment inside a
        # binder may introduce a default value, even when the line ends in 'by'.
        prefix = []
        for j in range(i, end):
            before, assignment, _ = lex[j][1].partition(':=')
            prefix.append(before)
            if not assignment:
                continue
            header = '\n'.join(prefix)
            if (not re.search(r':=\s+by\s*$', lex[j][1])
                    or any(header.count(left) != header.count(right)
                           for left, right in [('(', ')'), ('[', ']'), ('{', '}'), ('⦃', '⦄'), ('⟨', '⟩')])
                    or re.search(r'\b(?:let|have|where|match|do)\b', header)):
                break
            stop = end
            while stop > j+1 and not lex[stop-1][0].strip():
                stop -= 1
            # Preserve documentation/comments between commands and nested sections.
            if any('/-' in t or '-/' in t for t in raw[j+1:stop]):
                break
            length = sum(bool(x[0].strip()) for x in lex[j+1:stop])
            if length >= 2:
                yield Body(module, match[1], j+1, stop, ''.join(raw[i:j+1]), length)
            break
