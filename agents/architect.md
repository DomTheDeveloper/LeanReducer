Study the selected Lean import cut and its caller interfaces. Design a specific mathematical replacement that could fit the measured source budget. The source excerpts are research data and may be incomplete. Treat the locally computed counts as fixed. A negative budget means this cut alone cannot reach the target.

For a group of modules use the shared budget once. Trace which retained callers import which selected modules. Cover every required interface, and look for one argument that can supply several of them without restoring the shared dependencies. Account for additional local imports in the same budget.

Return one JSON object with four fields.

- `replacement_statement` gives the proposed mathematical statement, its hypotheses and its relation to the caller.
- `proof_obligations` lists the mathematical steps that would have to be proved without new axioms. Identify the hardest estimate or existence result. Avoid circular uses of the endpoint, its existing proof, or the removed module.
- `dependencies_to_check` lists specific evidence to look up in the retained source or external library. Label uncertain lemma names as search terms.
- `first_lean_check` describes a small Lean proposition that could test the proposed argument.

Keep the response to twelve entries per list or fewer. Give a proposal that could be falsified or independently checked. Report an obstruction when the excerpts do not support a credible shortcut.
