"""Index named declarations in the published kernel export with bounded I/O.

Stream the uncompressed NDJSON on stdin. The expected digest covers every byte.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

from leanreducer.source import DECL, lexical_lines

DIGEST = 'ab7b4223b9bd748a1aa68bdb63afb6d6264121fc834aadba7ba3d3796c32115b'
RECORD = re.compile(rb'^\{"(?:in|thm|def|inductive|opaque|axiom|quot)":.*$', re.M)
WORD = re.compile(r"[^\W\d][\w'₀-₉]*")


def exported_parts(stream, digest):
    hash_ = hashlib.sha256()
    names = {0: ''}
    components = set()
    kinds = Counter()
    tail = b''
    while True:
        block = stream.read(4 << 20)
        hash_.update(block)
        if block:
            chunk, tail = (tail + block).rsplit(b'\n', 1) if b'\n' in block else (b'', tail + block)
        else:
            chunk = tail
        for hit in RECORD.finditer(chunk):
            obj = json.loads(hit[0])
            key = next(iter(obj))
            v = obj[key]
            if key == 'in':
                a = obj.get('str') or obj['num']
                n = str(a.get('str', a.get('i')))
                pre = names[a['pre']]
                names[v] = (pre + '.' if pre else '') + n
            else:
                kinds[key] += 1
                indices = [t['name'] for t in v['types']] if key == 'inductive' else [v['name']]
                for i in indices:
                    components.update(names[i].split('.'))
        if not block:
            break
    if hash_.hexdigest() != digest:
        raise ValueError('incomplete or different solution export (SHA-256 mismatch)')
    return components, kinds


def scan(source, components):
    found, occurrences = [], Counter()
    for path in sorted(source.rglob('*.lean')):
        lines = list(lexical_lines(path.read_bytes().decode()))
        for _, tokens in lines:
            occurrences.update(WORD.findall(tokens))
        starts = [i for i, (_, s) in enumerate(lines) if s and s.strip() and not s[0].isspace()]
        for i, end in zip(starts, [*starts[1:],len(lines)]):
            command = DECL.match(lines[i][1])
            if command and (short := command[1].split('.')[-1]) not in components:
                size = sum(bool(code.strip()) for code,_ in lines[i:end])
                found.append({'path': str(path.relative_to(source)), 'line': i+1, 'name': command[1],
                              'short_name': short, 'code_lines': size})
    for row in found:
        row['spelling_occurrences'] = occurrences[row.pop('short_name')]
    return found


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('source', type=Path)
    args = p.parse_args()
    components, kinds = exported_parts(sys.stdin.buffer, DIGEST)
    if sum(kinds.values()) != 204583:
        sys.exit('unexpected record count')
    hits = scan(args.source, components)
    print(json.dumps({'export_sha256': DIGEST, 'declaration_records': kinds,
                      'absent_name_candidates': hits}, ensure_ascii=False, indent=2))
