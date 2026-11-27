"""Supply a mathematical replacement agent with the measured import cut and its callers."""
from . import agents


def excerpt(path, limit):
    source = path.read_text(encoding="utf-8")
    if len(source) <= limit:
        return {"complete": True, "source": source}
    half = limit // 2
    return {"complete": False, "start": source[:half], "end": source[-half:]}


def replacement_plan(corpus, entry, cut, counts, target, model, *, request=agents.ask):
    reachable = corpus.walk(entry)
    if cut not in reachable:
        raise ValueError(f"{cut} is outside the import closure of {entry}")
    if target < 0:
        raise ValueError("the source target must be nonnegative")
    remaining = corpus.walk(entry, (cut,))
    callers = sorted(module for module in remaining if cut in corpus.deps[module])
    # The budget includes every new local dependency required by the replacement.
    budget = target - counts["remaining_before_replacement"]["code"]
    payload = {
        "entry": entry, "cut": cut, "target_code_lines": target,
        "remaining_code_lines": counts["remaining_before_replacement"]["code"],
        "exclusive_code_lines": counts["exclusive_to_cut"]["code"],
        "replacement_budget": budget,
        "cut_source": excerpt(corpus.paths[cut], 18000),
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
    return {"status": "unverified research proposal", "cut": cut,
            "replacement_budget": budget, "direct_callers": callers, "proposal": answer}
