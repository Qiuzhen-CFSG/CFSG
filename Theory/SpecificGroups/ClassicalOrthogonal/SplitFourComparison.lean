/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.Representation.OrthogonalFourPlusMatrix.Comparison
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Split four-dimensional projective orthogonal groups over arbitrary fields

The existing left-right determinant action has exactly the elementary
Siegel subgroup as image. Its projective kernel is the product of the two
SL₂ centers: a scalar action on every two-by-two matrix forces each factor
to be scalar. The first isomorphism theorem therefore gives the actual
PΩ₄⁺(F) ≃ PSL₂(F) × PSL₂(F) comparison. The two nontrivial factors exclude
this carrier from the simple groups, including over odd fields.

Adapted from ATLAS `LinearGroups/Orthogonal/D2MatrixKernel.lean` and
`D2MatrixComparison.lean`. Changes: reuse CFSG's existing determinant
coordinates, elementary-image proof, and scalar quotient; Lean 4.33 module
syntax. No alternate orthogonal carrier or order comparison is introduced.
Source application: Aschbacher–Smith A.2.17, printed pp.38–39; GLS3 §2.7.
-/

public noncomputable section
namespace ClassicalOrthogonal.FourPlusMatrix
open Matrix
variable {F : Type*} [Field F]

/-- Scalar action on all determinant coordinates forces both SL2 factors to be central. -/
private theorem matrixAction_scalar_implies_centers (g : PairSL (F := F)) (c : F) (hc : c ≠ 0)
    (h : ∀ M : Mat (F := F), g.1.val*M*g.2⁻¹.val = c • M) :
    g.1 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ∧
      g.2 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hAB : g.1.val = c • g.2.val := by
    have ht := congrArg (fun M : Mat (F := F) => M*g.2.val) (h 1)
    rw [mul_one,mul_assoc,← Matrix.SpecialLinearGroup.coe_mul g.2⁻¹ g.2,
      inv_mul_cancel,Matrix.SpecialLinearGroup.coe_one,mul_one,smul_mul_assoc,one_mul] at ht
    exact ht
  have hcommB (M : Mat (F := F)) : g.2.val*M = M*g.2.val := by
    have ht := congrArg (fun N : Mat (F := F) => N*g.2.val) (h M)
    rw [mul_assoc,← Matrix.SpecialLinearGroup.coe_mul g.2⁻¹ g.2,
      inv_mul_cancel,Matrix.SpecialLinearGroup.coe_one,mul_one,hAB,smul_mul_assoc,smul_mul_assoc] at ht
    exact (smul_right_injective _ hc) ht
  constructor
  · rw [Subgroup.mem_center_iff]
    intro B
    apply Subtype.ext
    change B.val*g.1.val = g.1.val*B.val
    rw [hAB,smul_mul_assoc,mul_smul_comm,hcommB]
  · rw [Subgroup.mem_center_iff]
    intro B
    apply Subtype.ext
    exact (hcommB B.val).symm

/-- The actual projective action kernel forces scalar matrices in both factors. -/
private theorem toOrthogonal_scalar_implies_centers (g : PairSL (F := F)) (c : F) (hc : c ≠ 0)
    (h : ∀ v : VectorD 2 F, (toOrthogonal g).val v = c • v) :
    g.1 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ∧
      g.2 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  apply matrixAction_scalar_implies_centers g c hc
  intro M
  have ht := toOrthogonal_coordinates g (coordinates.symm M)
  rw [h,map_smul,LinearEquiv.apply_symm_apply] at ht
  exact ht.symm
end ClassicalOrthogonal.FourPlusMatrix

namespace ClassicalOrthogonal.FourPlusMatrix
open Matrix
variable {F : Type*} [Field F]

private theorem SL2_center_inv_eq_self (B : Matrix.SpecialLinearGroup (Fin 2) F)
    (hB : B ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) : B⁻¹ = B := by
  obtain ⟨b,hb,hs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hB
  have hb' : b^2 = 1 := by simpa using hb
  have hh : B*B = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul,← hs,← map_mul,← pow_two,hb',map_one]
    rfl
  exact inv_eq_of_mul_eq_one_right hh

/-- The full preimage of ambient scalar isometries is the product of the two SL2 centers. -/
theorem toOrthogonal_scalar_iff_centers (g : PairSL (F := F)) :
    (∃ c : F, c^2 = 1 ∧ ∀ v : VectorD 2 F, (toOrthogonal g).val v = c • v) ↔
      g.1 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ∧
      g.2 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  constructor
  · rintro ⟨c,hc,h⟩
    apply toOrthogonal_scalar_implies_centers g c _ h
    intro hz
    rw [hz,zero_pow (by decide : 2 ≠ 0)] at hc
    exact zero_ne_one hc
  · rintro ⟨hA,hB⟩
    obtain ⟨a,ha,hsa⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    obtain ⟨b,hb,hsb⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hB
    have ha' : a^2 = 1 := by simpa using ha
    have hb' : b^2 = 1 := by simpa using hb
    refine ⟨a*b,by rw [mul_pow,ha',hb',mul_one],?_⟩
    intro v
    apply coordinates.injective
    rw [toOrthogonal_coordinates,map_smul,SL2_center_inv_eq_self g.2 hB,← hsa,← hsb]
    ext i j
    simp [Matrix.scalar,Matrix.diagonal_mul,Matrix.mul_diagonal,smul_eq_mul]
    ring
end ClassicalOrthogonal.FourPlusMatrix

namespace ClassicalOrthogonal.FourPlusMatrix
open Matrix
variable {F : Type*} [Field F]

def toProjective : PairSL (F := F) →* ProjectiveElementary (formD 2 F) :=
  (projectiveElementaryMap _).comp toElementary

theorem toProjective_surjective : Function.Surjective (toProjective (F := F)) :=
  (projectiveElementaryMap_surjective _).comp toElementary_surjective

theorem toProjective_eq_one_iff_centers (g : PairSL (F := F)) :
    toProjective g = 1 ↔ g.1 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ∧
      g.2 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  change (QuotientGroup.mk (toElementary g) : ProjectiveElementary (formD 2 F)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  exact toOrthogonal_scalar_iff_centers g

theorem toProjective_kernel : (toProjective (F := F)).ker =
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)).prod
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) := by
  ext g
  exact toProjective_eq_one_iff_centers g

/-- The coordinatewise existing PSL₂ projections. -/
private def productProjection : PairSL (F := F) →*
    ProjectiveSpecialLinearGroup (Fin 2) F × ProjectiveSpecialLinearGroup (Fin 2) F :=
  (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).prodMap
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))

private theorem productProjection_surjective : Function.Surjective (productProjection (F := F)) := by
  rintro ⟨x,y⟩
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) x
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) y
  exact ⟨(a,b),rfl⟩

private theorem projective_kernels_eq : (toProjective (F := F)).ker = productProjection.ker := by
  ext g
  rw [MonoidHom.mem_ker, toProjective_eq_one_iff_centers]
  change _ ↔ ((QuotientGroup.mk g.1 : ProjectiveSpecialLinearGroup (Fin 2) F),
    (QuotientGroup.mk g.2 : ProjectiveSpecialLinearGroup (Fin 2) F)) = (1,1)
  rw [Prod.mk.injEq, QuotientGroup.eq_one_iff, QuotientGroup.eq_one_iff]

/-- The actual projective elementary split-D₂ model is the product PSL₂ × PSL₂. -/
def projectiveEquivProduct : ProjectiveElementary (formD 2 F) ≃*
    ProjectiveSpecialLinearGroup (Fin 2) F × ProjectiveSpecialLinearGroup (Fin 2) F :=
  (QuotientGroup.quotientKerEquivOfSurjective toProjective toProjective_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq projective_kernels_eq).trans
      (QuotientGroup.quotientKerEquivOfSurjective productProjection productProjection_surjective))

/-- The isomorphism agrees with the original two matrix factors on every lift. -/
theorem projectiveEquivProduct_projection (g : PairSL (F := F)) :
    projectiveEquivProduct (projectiveElementaryMap _ (toElementary g)) =
      (QuotientGroup.mk g.1, QuotientGroup.mk g.2) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective (toProjective (F := F)) toProjective_surjective
  change ((QuotientGroup.quotientMulEquivOfEq projective_kernels_eq).trans
    (QuotientGroup.quotientKerEquivOfSurjective productProjection productProjection_surjective))
      (e.symm (e (QuotientGroup.mk g))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

end ClassicalOrthogonal.FourPlusMatrix

namespace ClassicalOrthogonal.FourPlusMatrix
open Matrix
variable (F : Type*) [Field F]

/-- Both PSL₂ factors have a nonidentity transvection over every field. -/
theorem not_isSimpleGroup_pOmegaPlus_two : ¬ IsSimpleGroup (POmegaPlus 2 F) := by
  intro hsimp
  let := hsimp
  let S := ProjectiveSpecialLinearGroup (Fin 2) F
  let u : Matrix.SpecialLinearGroup (Fin 2) F :=
    Matrix.SpecialLinearGroup.transvection (i := 0) (j := 1) (by decide) 1
  let t : S := QuotientGroup.mk u
  have ht : t ≠ 1 := by
    intro he
    have hc : u ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
      (QuotientGroup.eq_one_iff u).mp he
    obtain ⟨c, _, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
    have hentry := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A 0 1) hc
    simp [u, Matrix.SpecialLinearGroup.transvection, Matrix.transvection, Matrix.scalar_apply]
      at hentry
  let : IsSimpleGroup (S × S) := (projectiveEquivProduct (F := F)).symm.isSimpleGroup
  let p : S × S →* S := MonoidHom.fst S S
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal p.ker inferInstance with hb | htop
  · have he : (1, t) ∈ p.ker := by change p (1, t) = 1; rfl
    rw [hb, Subgroup.mem_bot] at he
    exact ht (congrArg Prod.snd he)
  · have he : (t, 1) ∈ p.ker := htop ▸ Subgroup.mem_top _
    exact ht he

end ClassicalOrthogonal.FourPlusMatrix
