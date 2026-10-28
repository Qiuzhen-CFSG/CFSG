module
public import Theory.Representation.BinaryOffender.ComponentFixedLine
public import Theory.Representation.OrthogonalFourPlusMatrix.QuotientLocal.ComponentAction
import Mathlib.Tactic.FinCases

/-!
# Residual generation from the orthogonal fixed line

The cubic matrix with rows (0,1) and (1,1) has no nonzero fixed vectors
under left multiplication, or inverse right multiplication. Thus both
SL₂(4) factors move every nonzero matrix. If a normal determinant group
has an actor with a one-dimensional binary fixed space, the component
commutator theorem forces both factors into its commutator with that actor.

This supplies the literal orthogonal residual-generation step in
Aschbacher--Smith 14.4.7, printed p.1009, without choosing a factor swap.
The source consumer retains the original quotient and conjugator.
-/

public noncomputable section
namespace ClassicalOrthogonal.FourPlusMatrix.Binary
open Representation.BinaryOffender Subgroup Matrix

private def cubic : Representation.SL2FourNatural.SL :=
  ⟨!![0,1;1,1], by simp [Matrix.det_fin_two,CharTwo.neg_eq]⟩

private theorem left_cubic_fixed (M : V) (h : action (cubic,1) M = M) : M = 0 := by
  have he : cubic.val * M = M := by
    rw [action_apply, inv_one] at h
    change cubic.val * M * (1 : V) = M at h
    simpa only [mul_one] using h
  have h0 (j : Fin 2) : M 1 j = M 0 j := by
    simpa [cubic,Matrix.mul_apply,Fin.sum_univ_two] using congrArg (fun N : V => N 0 j) he
  have h1 (j : Fin 2) : M 0 j + M 1 j = M 1 j := by
    simpa [cubic,Matrix.mul_apply,Fin.sum_univ_two] using congrArg (fun N : V => N 1 j) he
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact add_right_cancel ((h1 j).trans (zero_add _).symm)
  · exact (h0 j).trans (add_right_cancel ((h1 j).trans (zero_add _).symm))

private theorem right_cubic_fixed (M : V) (h : action (1,cubic⁻¹) M = M) : M = 0 := by
  have he : M * cubic.val = M := by
    rw [action_apply, inv_inv] at h
    change (1 : V) * M * cubic.val = M at h
    simpa only [one_mul] using h
  have h0 (i : Fin 2) : M i 1 = M i 0 := by
    simpa [cubic,Matrix.mul_apply,Fin.sum_univ_two] using congrArg (fun N : V => N i 0) he
  have h1 (i : Fin 2) : M i 0 + M i 1 = M i 1 := by
    simpa [cubic,Matrix.mul_apply,Fin.sum_univ_two] using congrArg (fun N : V => N i 1) he
  apply Matrix.ext
  intro i j
  fin_cases j
  · exact add_right_cancel ((h1 i).trans (zero_add _).symm)
  · exact (h0 i).trans (add_right_cancel ((h1 i).trans (zero_add _).symm))

/-- The two actual determinant factors generate their normal product by
commutators with an actor having exactly one binary fixed line. -/
theorem commutator_eq_of_fixed_line {Q W : Type*} [Group Q]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) Q W) (K X : Subgroup Q) [K.Normal]
    (κ : K ≃* G) (e : W ≃ₗ[ZMod 2] V)
    (he : ∀ (k : K) w, e (ρ k w) = action (κ k) (e w))
    (v : W) (hv : v ≠ 0)
    (hf : fixedSpace ρ X = Submodule.span (ZMod 2) {v}) : ⁅K,X⁆ = K := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : Theory.GroupTheory.IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : Theory.GroupTheory.IsQuasisimple Representation.SL2FourNatural.SL :=
    Theory.GroupTheory.IsQuasisimple.of_mulEquiv QuotientLocal.factorAlternatingEquiv.symm
  apply product_commutator_eq_of_fixed_line ρ K X κ v hv hf
  · refine ⟨cubic, ?_⟩
    intro hh
    have hfix : action (cubic,1) (e v) = e v := by
      rw [← κ.apply_symm_apply (cubic,1), ← he, hh]
    exact hv (e.injective ((left_cubic_fixed (e v) hfix).trans e.map_zero.symm))
  · refine ⟨cubic⁻¹, ?_⟩
    intro hh
    have hfix : action (1,cubic⁻¹) (e v) = e v := by
      rw [← κ.apply_symm_apply (1,cubic⁻¹), ← he, hh]
    exact hv (e.injective ((right_cubic_fixed (e v) hfix).trans e.map_zero.symm))
end ClassicalOrthogonal.FourPlusMatrix.Binary
