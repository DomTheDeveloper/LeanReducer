"""Supply a mathematical replacement agent with the measured import cut and its callers."""
from . import agents


def excerpt(path, limit):
    source = path.read_text(encoding="utf-8")
    if len(source) <= limit:
        return {"complete": True, "source": source}
    tail = limit // 2
    return {"complete": False, "start": source[:limit - tail], "end": source[len(source) - tail:]}


def replacement_plan(corpus, entry, cut, counts, target, model, *, request=agents.ask):
    cuts = [cut] if isinstance(cut, str) else sorted(set(cut))
    if not cuts:
        raise ValueError("choose at least one module for a replacement")
    reachable = corpus.walk(entry)
    for name in cuts:
        if name not in reachable:
            raise ValueError(f"{name} is outside the import closure of {entry}")
    if target < 0:
        raise ValueError("the source target must be nonnegative")
    selected = set(cuts)
    remaining = corpus.walk(entry, selected)
    callers = sorted(module for module in remaining if selected.intersection(corpus.deps[module]))
    if len(cuts) == 1:
        selection = {"cut": cuts[0]}
        sources = {"cut_source": excerpt(corpus.paths[cuts[0]], 18000)}
        exclusive = counts["exclusive_to_cut"]["code"]
    else:
        selection = {"cuts": cuts}
        sources = {
            "cut_sources": {name: excerpt(corpus.paths[name], 18000 // len(cuts)) for name in cuts},
            "imports_by_caller": {name: sorted(selected.intersection(corpus.deps[name])) for name in callers},
            "code_released_by_no_single_cut": counts["released_by_no_single_cut"]["code"],
        }
        exclusive = counts["exclusive_to_joint_cut"]["code"]
    # The budget includes every new local dependency required by the replacement.
    budget = target - counts["remaining_before_replacement"]["code"]
    payload = {
        "entry": entry, **selection, **sources, "target_code_lines": target,
        "remaining_code_lines": counts["remaining_before_replacement"]["code"],
        "exclusive_code_lines": exclusive,
        "replacement_budget": budget,
        "caller_modules": callers,
        "caller_sources": {name: excerpt(corpus.paths[name], 4500) for name in callers[:4]},
    }
    answer = request("architect", model, payload)
    text_fields = {"replacement_statement", "first_lean_check"}
    list_fields = {"proof_obligations", "dependencies_to_check"}
    if not isinstance(answer, dict) or set(answer) != text_fields | list_fields:
        raise ValueError("invalid replacement proposal fields")
    for field in text_fields:
        if not isinstance(answer[field], str) or not answer[field].strip():
            raise ValueError(f"expected text for {field}")
    for field in list_fields:
        values = answer[field]
        if not isinstance(values, list) or len(values) > 12 or any(
            not isinstance(value, str) or not value.strip() for value in values
        ):
            raise ValueError(f"expected a list of up to twelve statements for {field}")
    if not answer["proof_obligations"]:
        raise ValueError("the proposed replacement needs an explicit proof obligation")
    return {"status": "unverified research proposal", **selection,
            "replacement_budget": budget, "direct_callers": callers, "proposal": answer}
