import PalomaMax2SAT
import Solution

open Lean Elab Command

/- Lists every theorem declared in the project modules whose axioms are not
among `propext`, `Classical.choice`, `Quot.sound`. Prints a summary and fails
if any such theorem exists. -/
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (n, ci) in env.constants.map₁.toList do
    unless ci matches .thmInfo _ do continue
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless (`PalomaMax2SAT).isPrefixOf modName || modName == `Solution do continue
    checked := checked + 1
    let axs ← liftCoreM <| collectAxioms n
    let extra := axs.filter (fun a => !allowed.contains a)
    unless extra.isEmpty do bad := bad.push (n, extra)
  logInfo m!"axiom check: {checked} theorems checked, {bad.size} with disallowed axioms"
  for (n, extra) in bad do
    logInfo m!"  {n}: {extra}"
  unless bad.isEmpty do
    throwError "axiom check failed"

-- Theorems named in comparator.json (CubicPublic namespace) and the UGC thresholds, for the log.
#print axioms PalomaMax2SAT.CubicPublic.repairedSet_independent
#print axioms PalomaMax2SAT.CubicPublic.exact_three_occurrence_identity
#print axioms PalomaMax2SAT.CubicPublic.ratio_83_84_from_cubic_mis
#print axioms PalomaMax2SAT.PaperArithmetic.ugc_thresholds
