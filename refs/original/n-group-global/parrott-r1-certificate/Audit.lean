module

public import Theory.SpecificGroups.Tits.R1Certificate.Verified
import Lean.Util.CollectAxioms

/-!
Audit the rebuilt certificate's public theorem dependencies. This command is
an inspection tool, not a proof rule; the certificate itself uses only ordinary
kernel-checked terms. Run after `lake build Theory.SpecificGroups.Tits.R1Certificate.Verified`.
-/

#print axioms Tits.R1Certificate.edges
#print axioms Tits.R1Certificate.inverse_table
#print axioms Tits.R1Certificate.initial_index
#print axioms Tits.R1Certificate.model
#print axioms Tits.parrottRelatorWord_eq
#print axioms Tits.parrottRelatorWord_eval

open Lean in
set_option maxHeartbeats 10000000 in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  -- Enumerate the exported families explicitly: module imports can load
  -- declarations lazily, so `env.constants.toList` is not a complete inventory.
  let mut names := #[`Tits.R1Certificate.model, `Tits.R1Certificate.relator_mem,
    `Tits.R1Certificate.initial_index, `Tits.R1Certificate.interval_join,
    `Tits.R1Certificate.interval_singleton, `Tits.R1Certificate.inverse_table,
    `Tits.R1Certificate.edges]
  for i in [:151167] do
    names := names.push (Name.str `Tits.R1Certificate s!"f{i}")
  for i in [:1755] do
    names := names.push (Name.str `Tits.R1Certificate s!"inverse_row_{i}")
    names := names.push (Name.str `Tits.R1Certificate s!"edges_row_{i}")
  for i in [:28] do
    names := names.push (Name.str `Tits.R1Certificate s!"inverse_interval_{64*i}")
    names := names.push (Name.str `Tits.R1Certificate s!"edges_interval_{64*i}")
  for name in names do
    unless (env.find? name).isSome do
      throwError "Missing certificate theorem: {name}"
    let axioms ← collectAxioms name
    unless axioms.all (fun ax => allowed.contains ax) do
      throwError "Unexpected axioms in {name}: {axioms}"
  logInfo m!"Audited {names.size} certificate theorems: only propext, Classical.choice, Quot.sound."
