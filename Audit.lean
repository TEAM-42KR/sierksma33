import SierksmaLean.Main
import Solution
import Lean

/-!
# Axiom and placeholder audit (part of the default build)

The build fails unless
1. every head theorem depends only on `propext`, `Classical.choice` and `Quot.sound`;
2. no constant of `SierksmaLean.*` uses `sorry` directly (the expected list below is empty).
-/

open Lean Elab Command

elab "#sierksma_audit" : command => do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let skeleton : Bool := false
  let expected : List Name := []
  let heads : List Name := [``SierksmaLean.main_theorem, ``SierksmaLean.sierksma_three_three, ``sierksma_three_three]
  for h in heads do
    let axs := (← liftCoreM <| Lean.collectAxioms h).toList
    logInfo m!"AUDIT axioms {h}: {axs}"
    for a in axs do
      unless std.contains a || (skeleton && a == ``sorryAx) do
        throwError m!"AUDIT FAIL {h}: forbidden axiom {a}"
    unless skeleton == axs.contains ``sorryAx do
      throwError m!"AUDIT FAIL {h}: sorryAx presence does not match the placeholder list"
  let mods := env.header.moduleNames
  let direct := env.constants.map₁.fold (init := (#[] : Array Name)) fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some idx =>
      if mods[idx.toNat]!.getRoot == `SierksmaLean && ci.getUsedConstantsAsSet.contains ``sorryAx then
        acc.push n
      else acc
    | none => acc
  let found := (direct.qsort Name.lt).toList
  let want := (expected.toArray.qsort Name.lt).toList
  logInfo m!"AUDIT placeholders ({found.length}): {found}"
  unless found == want do
    throwError m!"AUDIT FAIL placeholder mismatch (direct sorryAx users ≠ expected list): found {found}, expected {want}"

#sierksma_audit
