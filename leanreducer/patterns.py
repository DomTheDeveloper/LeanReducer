"""Find exact repeated Lean seal/unseal commands and their common project imports."""
from collections import defaultdict
from functools import lru_cache
from graphlib import CycleError, TopologicalSorter
import re

from .source import IDENT, imports, lexical_lines


def command_sites(source):
    lines = [s for _, s in lexical_lines(source)]
    for first, line in enumerate(lines):
        head = re.match(r'^(seal|unseal)\s+(.+)$', line)
        if not head:
            continue
        names = head[2].split()
        stop = first + 1
        while (names[-1] != 'in' and stop < len(lines) and lines[stop].strip()
               and lines[stop][0].isspace()):
            names.extend(lines[stop].split())
            stop += 1
        scoped = names[-1] == 'in'
        if scoped:
            names.pop()
        if names and all(re.fullmatch(IDENT, name) for name in names):
            yield (head[1], tuple(names)), {'line': first + 1, 'lines': stop - first, 'scoped': scoped}


def repeated_commands(corpus, entry):
    sites = defaultdict(list)
    for module in sorted(corpus.walk(entry)):
        for key, location in command_sites(corpus.paths[module].read_text()):
            sites[key].append({'module': module, **location})
    report = []
    for (command, names), uses in sites.items():
        if len(uses) < 2:
            continue
        gross = sum(u['lines'] - 1 for u in uses)
        if not gross:
            continue
        modules = {u['module'] for u in uses}
        common = set.intersection(*(corpus.walk(m) for m in modules))
        parents = {dep for m in common for dep in corpus.deps[m]}
        report.append({'command': command, 'identifiers': names, 'occurrences': len(uses),
                       'gross_call_site_lines_saved': gross, 'common_modules': sorted(common - parents),
                       'sites': uses})
    return sorted(report, key=lambda g: (-g['gross_call_site_lines_saved'], g['identifiers']))


def import_audit(corpus, entry):
    """Identify direct imports also available through other declared local imports."""
    direct = {m: imports(corpus.paths[m].read_text()) for m in corpus.walk(entry)}

    try:
        position = {name: i for i, name in enumerate(TopologicalSorter(direct).static_order())}
    except CycleError as exc:
        raise ValueError(f"cyclic Lean imports: {exc.args[1]}") from exc

    @lru_cache(maxsize=8192)
    def available_through(start, target):
        # A dependency is earlier in the topological order. Visit only modules
        # that can still reach the target, without retaining every ancestor set.
        pending, seen = [start], {start}
        while pending:
            current = pending.pop()
            if current == target:
                return True
            if position[current] <= position[target]:
                continue
            for dependency in direct.get(current, ()):
                if dependency not in seen and position[dependency] >= position[target]:
                    seen.add(dependency)
                    pending.append(dependency)
        return False

    redundant = []
    for module, deps in sorted(direct.items()):
        for i, dep in enumerate(deps):
            alternatives = [n for j, n in enumerate(deps) if i != j and available_through(n, dep)]
            if alternatives:
                redundant.append({'module': module, 'import': dep, 'also_via': alternatives})
    return {'direct_edges': sum(map(len, direct.values())), 'redundant': redundant}
