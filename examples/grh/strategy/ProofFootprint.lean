import RHOnly
import Lean

open Lean Elab Command

private def projectModule? (env : Environment) (c : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? c
  let mod ← env.header.moduleNames[idx.toNat]?
  guard ([`Lib, `New, `RHOnly, `RHCovolume].contains mod.getRoot)
  return mod

/-- Traverse the kernel expressions in project declarations. External modules are the boundary. -/
private partial def localClosure (env : Environment) (pending : List Name) (seen : NameSet) : NameSet :=
  match pending with
  | [] => seen
  | c :: rest => Id.run do
    if seen.contains c || (projectModule? env c).isNone then return localClosure env rest seen
    let some info := env.checked.get.find? c | return localClosure env rest (seen.insert c)
    let other := match info with
      | .inductInfo i => i.all
      | .ctorInfo i => [i.induct]
      | .recInfo i => i.rules.flatMap fun r => r.ctor :: r.rhs.getUsedConstants.toList
      | _ => []
    return localClosure env (other ++ info.getUsedConstantsAsSet.toList ++ rest) (seen.insert c)

run_cmd do
  let env := (← getEnv).setExporting false
  let used := localClosure env [``FixedClassRH.ordinaryRH] {}
  let mut rows : Array String := #[]
  for c in used do
    let some mod := projectModule? env c | continue
    let kind := match env.checked.get.find? c with
      | none => "missing"
      | some (.axiomInfo _) => "axiom"
      | _ => "decl"
    let range ← findDeclarationRanges? c
    let start := range.map (fun r => r.range.pos.line) |>.getD 0
    let stop := range.map (fun r => r.range.endPos.line) |>.getD 0
    rows := rows.push (String.intercalate "\t" [mod.toString, c.toString, kind, toString start, toString stop])
  liftIO <| IO.FS.writeFile "ordinary-rh-reach.tsv" (String.intercalate "\n" rows.toList)
