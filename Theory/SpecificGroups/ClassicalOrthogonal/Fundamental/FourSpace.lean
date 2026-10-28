/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The action-kernel calculation is adapted from
Atlas/LinearGroups/Orthogonal/D2MatrixKernel.lean. Changes: Lean 4.33 modules,
reuse CFSG's existing determinant action and elementary-image comparison,
and add the marked-factor, properness, and cubic-subgroup applications below.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.CubicObstruction
public import Theory.Representation.OrthogonalFourPlusMatrix.Comparison

/-!
# Marked SL₂ factors in the split four-space

The existing determinant action `M ↦ A M B⁻¹` maps onto the actual
Siegel-generated Ω₄⁺ carrier. Evaluating at the identity matrix and arbitrary
matrices shows that its kernel is precisely the diagonal scalar SL₂ center.
Thus both marked factors embed, commute, and generate the carrier. The first
is proper: the cubic matrix in the second factor is not scalar. The kernel
has exponent two, so the product of the two cubic cyclic subgroups gives an
actual elementary abelian subgroup of order nine.

These are the four-dimensional factors used to construct a fundamental
subgroup in larger orthogonal spaces. There is no projective injectivity claim
in dimension four: ambient extension by a nonzero complement is needed for
that part of Aschbacher–Smith A.2.17, printed p.39.
-/

public noncomputable section

open Matrix
namespace ClassicalOrthogonal.Fundamental
variable {F : Type*} [Field F]
open FourPlusMatrix

/-- Test the action kernel on the determinant matrix coordinates. -/
theorem fourAction_eq_one_iff (g : PairSL (F := F)) :
    toOrthogonal g = 1 ↔ ∀ M : Mat (F := F), g.1.val * M * g.2⁻¹.val = M := by
  constructor
  · intro hg M
    have h := toOrthogonal_coordinates g (coordinates.symm M)
    rw [hg] at h
    change coordinates (coordinates.symm M) =
      g.1.val * coordinates (coordinates.symm M) * g.2⁻¹.val at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  · intro hg
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply coordinates.injective
    exact (toOrthogonal_coordinates g v).trans (hg (coordinates v))

/-- The action kernel is the diagonal scalar SL₂ center. -/
theorem fourAction_kernel (g : PairSL (F := F)) :
    toOrthogonal g = 1 ↔
      g.1 = g.2 ∧ g.1 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  rw [fourAction_eq_one_iff]
  constructor
  · intro hg
    have hid := hg 1
    rw [mul_one] at hid
    have heq : g.1 = g.2 := by
      apply Subtype.ext
      have ht := congrArg (fun M : Mat (F := F) => M * g.2.val) hid
      rw [mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul g.2⁻¹ g.2, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, mul_one, one_mul] at ht
      exact ht
    refine ⟨heq, ?_⟩
    rw [Subgroup.mem_center_iff]
    intro B
    apply Subtype.ext
    have ht := congrArg (fun M : Mat (F := F) => M * g.2.val) (hg B.val)
    rw [mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul g.2⁻¹ g.2, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, mul_one, ← heq] at ht
    exact ht.symm
  · rintro ⟨heq, hcenter⟩ M
    obtain ⟨a, _, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcenter
    have hcomm : g.1.val * M = M * g.1.val := by
      rw [← hscalar]
      exact (Matrix.scalar_commute a (Commute.all a) M).eq
    rw [hcomm, heq, mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, mul_one]

/-- The existing action restricted to the actual elementary carrier. -/
abbrev fourMap : PairSL (F := F) →* OmegaPlus 2 F := FourPlusMatrix.toElementary

/-- The same exact kernel in the Omega codomain. -/
theorem fourMap_kernel (g : PairSL (F := F)) :
    fourMap g = 1 ↔ g.1 = g.2 ∧
      g.1 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  rw [← fourAction_kernel]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- The common scalar parameter in the two factors has square one. -/
theorem fourMap_kernel_scalar (g : PairSL (F := F)) :
    fourMap g = 1 ↔ ∃ c : F, c ^ 2 = 1 ∧
      Matrix.scalar (Fin 2) c = g.1.val ∧ Matrix.scalar (Fin 2) c = g.2.val := by
  rw [fourMap_kernel]
  constructor
  · rintro ⟨heq, hcenter⟩
    obtain ⟨c, hc, hs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcenter
    exact ⟨c, by simpa using hc, hs, heq ▸ hs⟩
  · rintro ⟨c, hc, h1, h2⟩
    refine ⟨Subtype.ext (h1.symm.trans h2), ?_⟩
    exact Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨c, by simpa using hc, h1⟩

/-- In particular the kernel cannot kill a nonidentity cubic element. -/
theorem fourMap_kernel_square (g : PairSL (F := F)) (hg : fourMap g = 1) :
    g ^ 2 = 1 := by
  obtain ⟨c, hc, h1, h2⟩ := (fourMap_kernel_scalar g).mp hg
  have hs (A : Matrix.SpecialLinearGroup (Fin 2) F) (hA : Matrix.scalar (Fin 2) c = A.val) :
      A ^ 2 = 1 := by
    apply Subtype.ext
    rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
      ← hA, ← map_mul, ← pow_two, hc, map_one]
  exact Prod.ext (hs g.1 h1) (hs g.2 h2)

/-- The left SL₂ factor on determinant space. -/
@[expose] def fourLeft : Matrix.SpecialLinearGroup (Fin 2) F →* OmegaPlus 2 F :=
  fourMap.comp (MonoidHom.inl _ _)

/-- The commuting right SL₂ factor on determinant space. -/
@[expose] def fourRight : Matrix.SpecialLinearGroup (Fin 2) F →* OmegaPlus 2 F :=
  fourMap.comp (MonoidHom.inr _ _)

/-- The left factor embeds in Omega before projectivization. -/
theorem fourLeft_injective : Function.Injective (fourLeft (F := F)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  exact ((fourMap_kernel (a, 1)).mp ha).1

/-- The right factor embeds in Omega before projectivization. -/
theorem fourRight_injective : Function.Injective (fourRight (F := F)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro b hb
  exact ((fourMap_kernel (1, b)).mp hb).1.symm

/-- The two marked factors commute in the actual carrier. -/
theorem fourFactors_commute (a b : Matrix.SpecialLinearGroup (Fin 2) F) :
    Commute (fourLeft a) (fourRight b) := by
  change fourMap (a, 1) * fourMap (1, b) = fourMap (1, b) * fourMap (a, 1)
  rw [← map_mul, ← map_mul]
  simp

/-- The action is multiplication of its marked commuting factors. -/
theorem fourMap_eq_mul (a b : Matrix.SpecialLinearGroup (Fin 2) F) :
    fourMap (a, b) = fourLeft a * fourRight b := by
  change fourMap (a, b) = fourMap (a, 1) * fourMap (1, b)
  rw [← map_mul]
  simp

/-- Every elementary isometry is a product of the two factors. -/
theorem fourMap_surjective : Function.Surjective (fourMap (F := F)) :=
  FourPlusMatrix.toElementary_surjective

/-- The two factors generate the full elementary carrier. -/
theorem fourFactors_generate :
    (fourLeft (F := F)).range ⊔ (fourRight (F := F)).range = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨⟨a, b⟩, rfl⟩ := fourMap_surjective g
  rw [fourMap_eq_mul]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨a, rfl⟩)
    (Subgroup.mem_sup_right ⟨b, rfl⟩)

private theorem cubicSL_not_center :
    cubicSL (F := F) ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  intro h
  obtain ⟨c, _, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have h10 := congrArg (fun M : Mat (F := F) => M 1 0) hc
  simp [cubicSL, Matrix.scalar, Matrix.diagonal] at h10

/-- A noncentral cubic in the right factor proves the left factor proper. -/
theorem fourLeft_proper : (fourLeft (F := F)).range ≠ ⊤ := by
  intro htop
  have hm : fourRight (cubicSL (F := F)) ∈ (fourLeft (F := F)).range :=
    htop ▸ Subgroup.mem_top _
  obtain ⟨a, ha⟩ := hm
  have hker : fourMap (a⁻¹, cubicSL) = 1 := by
    rw [fourMap_eq_mul, map_inv, ← ha, inv_mul_cancel]
  obtain ⟨heq, hc⟩ := (fourMap_kernel _).mp hker
  exact cubicSL_not_center (heq ▸ hc)

/-- An actual elementary abelian subgroup of order nine in Ω₄⁺ over every field. -/
theorem fourCover_contains_nine :
    ∃ E : Subgroup (OmegaPlus 2 F), IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨E, _, hE, hc⟩ := CubicProductQuotient.exists_nine (fourMap (F := F))
    fourMap_kernel_square cubicSL cubicSL cubicSL_order cubicSL_order
  exact ⟨E, hE, hc⟩

/-- The least-dimensional split complement used by A.2.17 contains a cubic. -/
theorem plusRankTwo_exists_cubic : ∃ b : OmegaPlus 2 F, orderOf b = 3 := by
  refine ⟨fourLeft cubicSL, ?_⟩
  exact (orderOf_injective fourLeft fourLeft_injective cubicSL).trans cubicSL_order

end ClassicalOrthogonal.Fundamental
