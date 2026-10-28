module

public import Theory.Representation.OrthogonalFourPlusMatrix.Binary
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Displacement in the determinant module over F₄

A nonidentity determinant-one matrix in characteristic two moves some line:
otherwise testing the two coordinate lines and their sum makes it scalar,
and its determinant makes that scalar one. If v and Av are independent, the
map w ↦ (A M B⁻¹ − M), with M = v wᵀ, is injective. The row space has binary
dimension four. Transposition gives the same argument for the other factor.
Opposite root groups also prove that the common fixed space is zero.

These are intrinsic facts of the literal SL₂(4) × SL₂(4) determinant action.
Identifying its image with the existing elementary orthogonal group remains a
separate obligation. Source: Aschbacher–Smith, 13.8.16(1), printed pp.952–953.
-/

@[expose] public section
namespace ClassicalOrthogonal.FourPlusMatrix.Displacement
open Matrix Module ClassicalOrthogonal.FourPlusMatrix

section Field
variable {K : Type*} [Field K] [CharP K 2]

private def wedge (v w : Fin 2 → K) : K := v 0 * w 1 - v 1 * w 0

private lemma exists_moved_line (A : SpecialLinearGroup (Fin 2) K) (hA : A ≠ 1) :
    ∃ v : Fin 2 → K, wedge v (A.val *ᵥ v) ≠ 0 := by
  by_contra! hh
  have h10 : A 1 0 = 0 := by
    simpa [wedge, mulVec, dotProduct, Fin.sum_univ_two] using hh ![1, 0]
  have h01 : A 0 1 = 0 := by
    simpa [wedge, mulVec, dotProduct, Fin.sum_univ_two] using hh ![0, 1]
  have he : A 1 1 = A 0 0 := by
    have h := hh ![1, 1]
    simpa [wedge, mulVec, dotProduct, Fin.sum_univ_two, h10, h01, sub_eq_zero] using h
  have hsq : A 0 0 ^ 2 = 1 := by
    simpa only [det_fin_two, h10, h01, he, mul_zero, sub_zero, pow_two] using A.property
  have ha : A 0 0 = 1 := CharTwo.sq_injective (by simpa using hsq)
  apply hA
  apply SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [h10, h01, he, ha]

private def outer (v : Fin 2 → K) : (Fin 2 → K) →ₗ[K] Mat (F := K) where
  toFun w := vecMulVec v w
  map_add' _ _ := vecMulVec_add _ _ _
  map_smul' c w := vecMulVec_smul c v w

omit [CharP K 2] in
private lemma outer_intertwiner_zero (A : SpecialLinearGroup (Fin 2) K)
    (B : Mat (F := K)) (v : Fin 2 → K) (hv : wedge v (A.val *ᵥ v) ≠ 0)
    (w : Fin 2 → K) (hw : A.val * outer v w = outer v w * B) : w = 0 := by
  change A.val * vecMulVec v w = vecMulVec v w * B at hw
  rw [mul_vecMulVec, vecMulVec_mul] at hw
  funext j
  have h0 := congrArg (fun M : Mat (F := K) => M 0 j) hw
  have h1 := congrArg (fun M : Mat (F := K) => M 1 j) hw
  change (A.val *ᵥ v) 0 * w j = v 0 * (w ᵥ* B) j at h0
  change (A.val *ᵥ v) 1 * w j = v 1 * (w ᵥ* B) j at h1
  have hz : wedge v (A.val *ᵥ v) * w j = 0 := by
    unfold wedge
    linear_combination v 0 * h1 - v 1 * h0
  exact (mul_eq_zero.mp hz).resolve_left hv

end Field

open ClassicalOrthogonal.FourPlusMatrix.Binary

/-- The fixed-matrix equation has no inverse after multiplication on the right. -/
theorem fixed_iff_intertwines (g : G) (M : V) :
    action g M = M ↔ g.1.val * M = M * g.2.val := by
  rw [action_apply]
  constructor
  · intro hh
    have ht := congrArg (fun X : V => X * g.2.val) hh
    simpa only [mul_assoc, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
      SpecialLinearGroup.coe_one, mul_one] using ht
  · intro hh
    rw [hh, mul_assoc, ← SpecialLinearGroup.coe_mul, mul_inv_cancel,
      SpecialLinearGroup.coe_one, mul_one]

/-- A nonidentity first factor displaces a binary four-space injectively. -/
theorem displacement_rank_four_left (g : G) (hg : g.1 ≠ 1) :
    4 ≤ finrank (ZMod 2) (LinearMap.range (action g - LinearMap.id)) := by
  obtain ⟨v, hv⟩ := exists_moved_line g.1 hg
  let f := (action g - LinearMap.id).comp ((outer v).restrictScalars (ZMod 2))
  have hf : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    change action g (outer v w) - outer v w = 0 at hw
    exact outer_intertwiner_zero g.1 g.2.val v hv w
      ((fixed_iff_intertwines g _).mp (sub_eq_zero.mp hw))
  have hr := Submodule.finrank_mono
    (LinearMap.range_comp_le_range ((outer v).restrictScalars (ZMod 2))
      (action g - LinearMap.id))
  have he := LinearMap.finrank_range_of_inj hf
  rw [show finrank (ZMod 2) (Fin 2 → F) = 4 from
    Representation.SL2FourNatural.finrank_vector] at he
  exact he.symm.trans_le hr

/-- The transposed argument applies to a nonidentity second factor. -/
theorem displacement_rank_four_right (g : G) (hg : g.2 ≠ 1) :
    4 ≤ finrank (ZMod 2) (LinearMap.range (action g - LinearMap.id)) := by
  have hgT : g.2.transpose ≠ 1 := by
    intro hh
    apply hg
    apply Subtype.ext
    have ht := congrArg (fun A : SpecialLinearGroup (Fin 2) F => A.val.transpose) hh
    simpa using ht
  obtain ⟨v, hv⟩ := exists_moved_line g.2.transpose hgT
  let outerT := (Matrix.transposeLinearEquiv (Fin 2) (Fin 2) F F).toLinearMap.comp (outer v)
  let f := (action g - LinearMap.id).comp (outerT.restrictScalars (ZMod 2))
  have hf : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    change action g (outer v w).transpose - (outer v w).transpose = 0 at hw
    have hh := (fixed_iff_intertwines g _).mp (sub_eq_zero.mp hw)
    have ht := congrArg Matrix.transpose hh
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at ht
    exact outer_intertwiner_zero g.2.transpose g.1.val.transpose v hv w ht.symm
  have hr := Submodule.finrank_mono
    (LinearMap.range_comp_le_range (outerT.restrictScalars (ZMod 2))
      (action g - LinearMap.id))
  have he := LinearMap.finrank_range_of_inj hf
  rw [show finrank (ZMod 2) (Fin 2 → F) = 4 from
    Representation.SL2FourNatural.finrank_vector] at he
  exact he.symm.trans_le hr

/-- Every nonidentity element of the determinant action has displacement rank
at least four over F₂; no involution hypothesis is needed. -/
theorem displacement_rank_four (g : G) (hg : g ≠ 1) :
    4 ≤ finrank (ZMod 2) (LinearMap.range (action g - LinearMap.id)) := by
  by_cases h1 : g.1 = 1
  · apply displacement_rank_four_right g
    intro h2
    exact hg (Prod.ext h1 h2)
  · exact displacement_rank_four_left g h1

/-- The two opposite root groups already have zero common fixed space. -/
theorem common_fixed_eq_zero (M : V) (hM : ∀ g : G, action g M = M) : M = 0 := by
  have hu := hM (Representation.SL2FourNatural.upper 1, 1)
  have hl := hM (SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) 1, 1)
  rw [fixed_iff_intertwines] at hu hl
  simp only [SpecialLinearGroup.coe_one, mul_one] at hu hl
  apply Matrix.ext
  intro i j
  fin_cases i
  · have h := congrArg (fun N : V => N 1 j) hl
    simpa [SpecialLinearGroup.transvection_coe, Matrix.transvection,
      Matrix.mul_apply, Fin.sum_univ_two] using h
  · have h := congrArg (fun N : V => N 0 j) hu
    simpa [Representation.SL2FourNatural.upper,
      Matrix.mul_apply, Fin.sum_univ_two] using h

end ClassicalOrthogonal.FourPlusMatrix.Displacement
