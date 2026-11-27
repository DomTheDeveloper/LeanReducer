import RHOnly
import Lean

open Lean Elab Command

/-- Positions of explicit arguments that occur in neither the remaining type nor the proof. -/
private partial def unusedArguments (type proof : Expr) (position : Nat := 0) : List (Nat × Name) :=
  match type, proof with
  | .forallE name _ rest info, .lam _ _ body _ =>
    let later := unusedArguments rest body (position + 1)
    if info.isExplicit && !rest.hasLooseBVar 0 && !body.hasLooseBVar 0
    then (position, name) :: later else later
  | _, _ => []

run_cmd do
  let env := (← getEnv).setExporting false
  let mut rows : Array String := #[]
  for (name, decl) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless [`Lib, `New, `RHOnly, `RHCovolume].contains mod.getRoot do continue
    let .thmInfo thm := decl | continue
    if name.isInternal || name.isImplementationDetail then continue
    for (position, binder) in unusedArguments thm.type thm.value do
      rows := rows.push (String.intercalate "\t" [mod.toString, name.toString, toString position, binder.toString])
  liftIO <| IO.FS.writeFile "unused-arguments.tsv" (String.intercalate "\n" rows.toList)
