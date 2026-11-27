"""Measure shared imports released by changing more than one module."""
from functools import reduce
from graphlib import TopologicalSorter
from itertools import combinations
from math import comb
from operator import and_


def joint_cut(corpus, entry, modules):
    modules = set(modules)
    reachable = corpus.walk(entry)
    kept = corpus.walk(entry, modules)
    released = reachable - kept
    released_individually = set()
    requiring_every_cut = released.copy()
    for module in modules:
        released_individually.update(reachable - corpus.walk(entry, (module,)))
        requiring_every_cut.intersection_update(corpus.walk(entry, modules - {module}))
    return {
        "modules": sorted(modules),
        "exclusive_to_joint_cut": corpus.size(released),
        "released_by_no_single_cut": corpus.size(released - released_individually),
        "requiring_every_cut": corpus.size(requiring_every_cut),
        "remaining_before_replacement": corpus.size(kept),
    }


def _after_cuts(parents, weights, fixed):
    """Return retained lines and each possible last cut's additional savings."""
    count = len(parents)
    dominators = [0] * count
    immediate = [-1] * count
    savings = [0] * count
    retained = 0
    for vertex, incoming in enumerate(parents):
        if vertex in fixed:
            continue
        # A bit is set if every surviving path from the entry passes that vertex.
        paths = [dominators[p] for p in incoming if dominators[p]]
        if incoming and not paths:
            continue
        common = reduce(and_, paths) if paths else 0
        dominators[vertex] = common | (1 << vertex)
        # Common dominators form a chain. Topological order puts the nearest last.
        immediate[vertex] = common.bit_length() - 1
        savings[vertex] = weights[vertex]
        retained += weights[vertex]

    for vertex in reversed(range(count)):
        parent = immediate[vertex]
        if parent >= 0:
            savings[parent] += savings[vertex]
    return retained, savings


def combination_audit(corpus, entry, target, excluded=(), *, size=2):
    if size not in (2, 3):
        raise ValueError("choose a pair or a triple")
    label = "pair" if size == 2 else "triple"
    reachable = corpus.walk(entry)
    excluded = set(excluded) | {entry}
    if excluded - reachable:
        raise ValueError("cut exclusions must be reachable from the entry")
    importers = {name: [] for name in sorted(reachable)}
    for caller in sorted(reachable):
        for dependency in corpus.deps[caller]:
            importers[dependency].append(caller)
    order = list(TopologicalSorter(importers).static_order())
    index = {name: position for position, name in enumerate(order)}
    parents = [[index[p] for p in importers[name]] for name in order]
    weights = [corpus.sizes[name]["code"] for name in order]
    choices = [i for i, name in enumerate(order) if name not in excluded]

    best = None
    passing = 0
    examples = []
    for positions in combinations(range(len(choices) - 1), size - 1):
        fixed = tuple(choices[i] for i in positions)
        retained, savings = _after_cuts(parents, weights, fixed)
        for last in choices[positions[-1] + 1:]:
            remaining = retained - savings[last]
            passing += remaining <= target
            sample = size == 3 and remaining <= target and len(examples) < 10
            if sample or best is None or remaining <= best[0]:
                group = tuple(sorted(order[v] for v in (*fixed, last)))
                candidate = (remaining, group)
                if sample:
                    examples.append(group)
                if best is None or candidate < best:
                    best = candidate

    result = {
        "excluded": sorted(excluded), "target_code_lines": target,
        f"{label}s_examined": comb(len(choices), size),
        f"{label}s_meeting_target_before_replacement": passing,
        f"best_{label}": joint_cut(corpus, entry, best[1]) if best else None,
    }
    if size == 3:
        result["first_matching_triples"] = [joint_cut(corpus, entry, group) for group in examples]
    return result


def pair_audit(corpus, entry, target, excluded=()):
    return combination_audit(corpus, entry, target, excluded)
