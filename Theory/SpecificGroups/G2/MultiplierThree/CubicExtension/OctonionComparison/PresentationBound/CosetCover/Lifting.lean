module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Checks

/-!
# Schreier relations in the original presented group

Every signed edge is identified with an actual group element by a checked
free-word identity. The edge products telescope, so the six original source
relations yield all 2184 relator equations. The two protected loops evaluate
to precisely the unchanged ATLAS max3 subgroup generators.

These equations are inputs to the separate algebraic generation proof; no
permutation-image order is used to infer an equality in the presented group.
Source: the elementary Schreier rewriting argument and `source/README.md`.
-/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover
open Subgroup.CosetWordCertificate

theorem edge_sound (i : Fin 364) (a : Letter Bool) :
    eval rawGenerator (edgeWord i a) =
      edgeElement representative Presentation.generator i a (next i a) :=
  edge_sound_of_check i a (edges_checked i a)

theorem eval_rawTrace (i : Nat) (hi : i < 364) (w : Word Bool) :
    eval rawGenerator (rawTrace i w) = representative i * eval Presentation.generator w *
      (representative (traceEnd next i w))⁻¹ := by
  induction w generalizing i with
  | nil => simp [rawTrace, traceEnd]
  | cons a w ih =>
    rw [rawTrace, eval_append, edge_sound ⟨i, hi⟩ a,
      ih (next i a) (Nat.mod_lt _ (by decide))]
    simp only [traceEnd, edgeElement, eval_cons]
    simp [mul_assoc]

/-- All equations for the generation certificate hold on the actual raw words. -/
theorem rawRelations : RawRelations rawGenerator := by
  constructor
  · intro i r
    rw [eval_rawTrace i i.isLt, relatorLetters_eq_one, relators_loop]
    simp
  · intro b
    rw [eval_rawTrace 0 (by decide), protected_loop, rawGenerator_protected,
      eval_boundLetters]
    change 1 * boundGenerator b * 1⁻¹ = boundGenerator b
    simp

/-- Actual raw-generator membership supplies all signed transition witnesses. -/
def coverOfMembership (hmem : ∀ k, rawGenerator k ∈ boundSubgroup) :
    Subgroup.GeneratorCosetCover boundSubgroup Presentation.generator (Fin 364) where
  repr i := representative i
  initial := 0
  initial_eq := rfl
  step i s := by
    have h : Holds boundSubgroup Presentation.generator representative
        ⟨i, [(s, true)], next i (s, true)⟩ := by
      apply (holds_iff_schreier_mem _ _ _ _).mpr
      change edgeElement representative Presentation.generator i (s, true)
        (next i (s, true)) ∈ boundSubgroup
      rw [← edge_sound i (s, true)]
      exact eval_mem_of_generators_mem _ _ hmem _
    obtain ⟨h, hh⟩ := h
    exact ⟨h, dest i (s, true), by simpa [dest] using hh⟩
  inv_step i s := by
    have h : Holds boundSubgroup Presentation.generator representative
        ⟨i, [(s, false)], next i (s, false)⟩ := by
      apply (holds_iff_schreier_mem _ _ _ _).mpr
      change edgeElement representative Presentation.generator i (s, false)
        (next i (s, false)) ∈ boundSubgroup
      rw [← edge_sound i (s, false)]
      exact eval_mem_of_generators_mem _ _ hmem _
    obtain ⟨h, hh⟩ := h
    exact ⟨h, dest i (s, false), by simpa [dest] using hh⟩

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover
