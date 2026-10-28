module

public import Theory.SpecificGroups.G2Five.AtlasBoundCertificate.SchreierRawData

/-!
# Soundness assembly for the recorded Schreier collapse

The argument has two independent inputs: honest raw tree/inverse-edge equations
and a replay of the short-relation collapse in any interpretation of the raw
alphabet. `witness_of_raw_collapse` combines them. Telescoping proves all original
relator equations once their finite endpoints have been checked; the two
protected endpoints are checked here directly by kernel reduction.

The selected raw edge values agree with `reducedGenerators` in the unchanged
ATLAS presentation. Thus the abstract collapse equations give `EdgeSound`, and
no subgroup finiteness or permutation faithfulness enters the proof.

Source: `SchreierSource/README.md` and the elementary telescoping theorem in
`Theory/GroupTheory/CosetWordCertificate/Schreier.lean`.
-/

@[expose] public section

open Subgroup.CosetWordCertificate
namespace G2Five.AtlasPresentation.SchreierBoundData

set_option maxRecDepth 10000 in
/-- Every selected reduced label names a vertex in the finite table. -/
theorem choices_bounded : ∀ k : ReducedAlphabet, (choices k.val).1 / 4 < 3906 := by
  decide +kernel

set_option maxRecDepth 10000 in
/-- Both protected subgroup words close at the root of the candidate table. -/
theorem protected_loops : ProtectedLoops := by
  unfold ProtectedLoops
  decide +kernel

/-- Raw edge soundness identifies the two definitions of reduced generators. -/
theorem selected_raw_eq (hraw : RawEdgeSound) :
    collapseGenerators rawGenerators = reducedGenerators := by
  funext k
  unfold collapseGenerators reducedGenerators
  split
  · exact rawGenerators_protected false
  · split
    · exact rawGenerators_protected true
    · dsimp only
      rw [hraw ⟨(choices k.val).1 / 4, choices_bounded k⟩]

/-- Any sound edge encoding telescopes along a word in the original generators. -/
theorem eval_trace_of_edges {α : Type*} (x : α → Model)
    (edge : Nat → Letter Bool → Word α) (trace : Nat → Word Bool → Word α)
    (hnil : ∀ i, trace i [] = [])
    (hcons : ∀ i a w, trace i (a :: w) = edge i a ++ trace (next i a) w)
    (hedge : ∀ (i : Fin 3906) (a : Letter Bool), eval x (edge i a) =
      edgeElement representative BoundCertificate.generators i (liftLetter a) (next i a))
    (i : Nat) (hi : i < 3906) (w : Word Bool) :
    eval x (trace i w) = representative i * eval generator w *
      (representative (traceEnd next i w))⁻¹ := by
  induction w generalizing i with
  | nil => simp [hnil, traceEnd]
  | cons a w ih =>
    rw [hcons, eval_append, hedge ⟨i, hi⟩ a,
      ih (next i a) (Nat.mod_lt _ (by decide))]
    simp only [traceEnd, edgeElement, eval_cons, liftLetter,
      BoundCertificate.generators]
    simp [mul_assoc]

theorem reduced_relations_of_edge_sound_of_loops
    (hedge : EdgeSound) (hrel : RelatorLoops) (hprot : ProtectedLoops) :
    ReducedRelations reducedGenerators := by
  constructor
  · intro i r
    rw [eval_trace_of_edges reducedGenerators edgeWord reducedTrace
      (fun _ => rfl) (fun _ _ _ => rfl) hedge i i.isLt]
    rw [show eval generator (boundLetters (word r)) = 1 from
      boundLetters_relator_eq_one r, hrel]
    simp
  · intro b
    rw [eval_trace_of_edges reducedGenerators edgeWord reducedTrace
      (fun _ => rfl) (fun _ _ _ => rfl) hedge 0 (by decide)]
    rw [hprot]
    simp only [representative, Definitions.repr_zero, one_mul, inv_one, mul_one,
      reducedGenerators_protected]
    rfl

theorem raw_relations_of_edge_sound_of_loops
    (hedge : RawEdgeSound) (hrel : RelatorLoops) (hprot : ProtectedLoops) :
    RawRelations rawGenerators := by
  constructor
  · intro i r
    rw [eval_trace_of_edges rawGenerators rawEdgeWord rawTrace
      (fun _ => rfl) (fun _ _ _ => rfl) hedge i i.isLt]
    rw [show eval generator (boundLetters (word r)) = 1 from
      boundLetters_relator_eq_one r, hrel]
    simp
  · intro b
    rw [eval_trace_of_edges rawGenerators rawEdgeWord rawTrace
      (fun _ => rfl) (fun _ _ _ => rfl) hedge 0 (by decide)]
    rw [hprot]
    simp only [representative, Definitions.repr_zero, one_mul, inv_one, mul_one,
      rawGenerators_protected]
    rfl

theorem edge_sound_of_raw_collapse (hraw : RawEdgeSound)
    (hcollapse : ∀ (i : Fin 3906) (a : Letter Bool),
      eval (collapseGenerators rawGenerators) (edgeWord i a) =
        eval rawGenerators (rawEdgeWord i a)) : EdgeSound := by
  intro i a
  rw [← selected_raw_eq hraw]
  exact (hcollapse i a).trans (hraw i a)

/-- Final assembly from the independent geometric and algebraic certificates. -/
theorem witness_of_raw_collapse (hraw : RawEdgeSound) (hloop : RelatorLoops)
    (hcollapse : RawRelations rawGenerators → ∀ (i : Fin 3906) (a : Letter Bool),
      eval (collapseGenerators rawGenerators) (edgeWord i a) =
        eval rawGenerators (rawEdgeWord i a)) :
    EdgeSound ∧ ReducedRelations reducedGenerators := by
  have he := edge_sound_of_raw_collapse hraw
    (hcollapse (raw_relations_of_edge_sound_of_loops hraw hloop protected_loops))
  exact ⟨he, reduced_relations_of_edge_sound_of_loops he hloop protected_loops⟩

end G2Five.AtlasPresentation.SchreierBoundData
