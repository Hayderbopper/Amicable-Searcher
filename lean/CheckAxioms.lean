/-
  Trust check, run by check.sh / check.ps1 with `lake env lean CheckAxioms.lean`.

  For every theorem declared in an `AmicableProof` module it prints the axioms the theorem
  depends on (what `#print axioms` prints), and it fails if
  * a theorem depends on anything but `propext`, `Classical.choice`, `Quot.sound`
    (in particular on `sorryAx`, or on `Lean.ofReduceBool` from `native_decide`), or
  * a module declares an axiom, an `unsafe` constant, or uses `implemented_by` / `extern`.
-/
import AmicableProof
import Lean.Util.CollectAxioms
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr

open Lean Elab Command

elab "#audit_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array String := #[]
  let mut lines : Array (String × String) := #[]
  for (name, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless (`AmicableProof).isPrefixOf modName do continue
    if name.isInternal then continue
    if ci.isUnsafe then bad := bad.push s!"unsafe constant: {name}"
    if (Compiler.getImplementedBy? env name).isSome then
      bad := bad.push s!"implemented_by: {name}"
    if isExtern env name then bad := bad.push s!"extern: {name}"
    match ci with
    | .axiomInfo _ => bad := bad.push s!"axiom declared: {name}"
    | .thmInfo _ =>
      let axs ← collectAxioms name
      let axs := axs.qsort (fun a b => a.toString < b.toString)
      for a in axs do
        unless allowed.contains a do bad := bad.push s!"{name} depends on {a}"
      let shown := if axs.isEmpty then "(no axioms)" else ", ".intercalate (axs.toList.map toString)
      -- theorems written in the source have a declaration range; generated equation lemmas,
      -- `sizeOf_spec`, `inj`, … do not (they are still checked)
      let declared := (← findDeclarationRanges? name).isSome
      let tag := if declared then "" else "  [generated]"
      lines := lines.push (name.toString, s!"{modName}  {name}: {shown}{tag}")
    | _ => pure ()
  let sorted := lines.qsort (fun a b => a.1 < b.1)
  for (_, l) in sorted do logInfo l
  if bad.isEmpty then
    logInfo s!"AXIOM CHECK OK: {sorted.size} theorems; every one uses at most propext, Classical.choice, Quot.sound; no axiom/unsafe/implemented_by/extern declarations."
  else
    throwError s!"AXIOM CHECK FAILED:\n{"\n".intercalate bad.toList}"

#audit_axioms
