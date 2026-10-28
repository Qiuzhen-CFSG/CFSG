module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover
import Lean.Util.CollectAxioms

/-! Inspection of every exported proof in the J₃ M₁ cover certificate.
This command is not a proof rule; acceptance uses ordinary kernel-checked terms. -/

#print axioms Sporadic.Janko3.RecognitionPresentation.OrderBound.m1Cover
#print axioms Sporadic.Janko3.RecognitionPresentation.OrderBound.m1_finiteIndex
#print axioms Sporadic.Janko3.RecognitionPresentation.OrderBound.m1_index_le
#print axioms Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate.all_hold
#print axioms Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate.all_shapes

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let ns := `Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
  let mut names := #[`Sporadic.Janko3.RecognitionPresentation.OrderBound.m1Cover,
    `Sporadic.Janko3.RecognitionPresentation.OrderBound.m1_finiteIndex,
    `Sporadic.Janko3.RecognitionPresentation.OrderBound.m1_index_le]
  for s in #["eval_rotate", "rotatedRelator_valid", "context_valid", "shapeChunk_sound",
      "output_lt", "all_hold", "all_shapes"] do
    names := names.push (Name.str ns s)
  for s in #["pathCheck_sound", "check_sound", "chunk_sound"] do
    names := names.push (Name.str (Name.str ns "Scan") s)
  for i in [:271] do
    names := names.push (Name.str ns s!"checked_{1024*i}")
  for i in [:17] do
    names := names.push (Name.str ns s!"sound_{16384*i}")
  for i in [:25] do
    names := names.push (Name.str ns s!"shaped_{1024*i}")
  for name in names do
    unless (env.find? name).isSome do
      throwError "Missing certificate export: {name}"
    let axioms ← collectAxioms name
    unless axioms.all (fun ax => allowed.contains ax) do
      throwError "Unexpected axioms in {name}: {axioms}"
  logInfo m!"Audited {names.size} exports: only propext, Classical.choice, Quot.sound."
