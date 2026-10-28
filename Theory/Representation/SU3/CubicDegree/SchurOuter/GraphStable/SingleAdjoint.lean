module

public import Theory.Representation.SL3.BinaryDefiningFactors.SmallPatterns

/-!
# Removing trivial factors from a single-adjoint word

A tensor word with no natural labels and one adjoint label is the actual
adjoint representation at the embedding twisted by that label's position.
The proof removes tensor units on both sides, retaining the intertwiner.

This is the final representation construction in Guralnick--Malle,
Classification of 2F-modules II, Proposition 4.11, internal pp.31--32.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Representation
open scoped MatrixGroups TensorProduct
namespace Representation.SU3.CubicDegree.SchurOuter.GraphStable
open Representation.SL3.BinaryDefiningFactors

variable {F K : Type*} [Field F] [Field K] [CharP K 2]

private theorem trivial_word_equiv (ι : F →+* K) (w : List Factor)
    (hn : naturalCount w = 0) (ha : adjointCount w = 0) :
    Nonempty ((wordRep ι w).Equiv (Representation.trivial K SL(3,F) K)) := by
  induction w generalizing ι with
  | nil => exact ⟨Representation.Equiv.refl _⟩
  | cons a w ih =>
    cases a with
    | trivial =>
      have hn' : naturalCount w = 0 := by simpa [naturalCount] using hn
      have ha' : adjointCount w = 0 := by simpa [adjointCount] using ha
      obtain ⟨e⟩ := ih ((frobenius K 2).comp ι) hn' ha'
      exact ⟨(Representation.TensorProduct.lid K _).trans e⟩
    | natural => simp [naturalCount] at hn
    | dual => simp [naturalCount] at hn
    | adjoint => simp [adjointCount] at ha

/-- The single surviving adjoint factor retains its precise Frobenius position. -/
theorem wordRep_single_adjoint_uniform (w : List Factor)
    (hn : naturalCount w = 0) (ha : adjointCount w = 1) :
    ∃ j : ℕ, j < w.length ∧ ∀ ι : F →+* K,
      Nonempty ((wordRep ι w).Equiv
        (factorRep ((iterateFrobenius K 2 j).comp ι) .adjoint)) := by
  induction w with
  | nil => simp [adjointCount] at ha
  | cons a w ih =>
    cases a with
    | trivial =>
      have hn' : naturalCount w = 0 := by simpa [naturalCount] using hn
      have ha' : adjointCount w = 1 := by simpa [adjointCount] using ha
      obtain ⟨j, hj, he⟩ := ih hn' ha'
      refine ⟨j + 1, by simpa using Nat.succ_lt_succ hj, ?_⟩
      intro ι
      obtain ⟨e⟩ := he ((frobenius K 2).comp ι)
      refine ⟨?_⟩
      change ((Representation.trivial K SL(3,F) K).tprod
        (wordRep ((frobenius K 2).comp ι) w)).Equiv
          (factorRep ((iterateFrobenius K 2 (j + 1)).comp ι) .adjoint)
      rw [iterateFrobenius_add, iterateFrobenius_one, RingHom.comp_assoc]
      exact (Representation.TensorProduct.lid K _).trans e
    | natural => simp [naturalCount] at hn
    | dual => simp [naturalCount] at hn
    | adjoint =>
      have hn' : naturalCount w = 0 := by simpa [naturalCount] using hn
      have ha' : adjointCount w = 0 := by simpa [adjointCount] using ha
      refine ⟨0, by simp, ?_⟩
      intro ι
      obtain ⟨e⟩ := trivial_word_equiv ((frobenius K 2).comp ι) w hn' ha'
      refine ⟨?_⟩
      simpa [wordRep] using
        (tensorRightEquiv e).trans (Representation.TensorProduct.rid K (factorRep ι .adjoint))

end Representation.SU3.CubicDegree.SchurOuter.GraphStable
