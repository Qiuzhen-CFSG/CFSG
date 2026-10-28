module

public import Theory.Representation.SymplecticFourOrthogonalCover.SylowFlag.Natural

/-!
# Fixed preimages, singular complements, and the literal transvection root

A fixed natural vector has zero quadratic correction, so every lift of it is
fixed. The standard first preimage is consequently a two-space, the direct
sum of the radical and its unique singular projective point. The actual root
intersection lies in the intrinsic center of the standard derived Sylow.

Source: Aschbacher–Smith, I.2.3(1a),(2), printed p.413 / PDF p.424.
-/

@[expose] public section
noncomputable section
open Matrix Subgroup
open Representation.OneCohomology
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
namespace Representation.SymplecticFourOrthogonalCover.SylowFlag
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
set_option linter.unusedSectionVars false

/-- The singular projective point above the standard natural line. -/
def singularPoint : Submodule K (Space (K := K)) :=
  (firstLine (K := K)).prod ⊥

lemma correction_eq_zero_of_fixed (g : Sp K) (v : Natural (K := K))
    (hv : g.val *ᵥ v = v) : correction g v = 0 := by
  have h := correction_square g v
  rw [hv] at h
  exact (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp (add_eq_left.mp h.symm)

/-- The orthogonal lift fixes precisely the full preimage of the natural fixed space. -/
lemma fixed_preimage (H : Subgroup (L (K := K))) :
    fixed ((action (K := K)).comp H.subtype) =
      (fixed ((symplecticDerivedNatural 2).comp H.subtype)).comap projection.toLinearMap := by
  ext x
  constructor
  · intro hx g
    exact congrArg Prod.fst (hx g)
  · intro hx g
    have hv : g.val.val.val *ᵥ x.1 = x.1 := hx g
    change action g.val x = x
    rw [action_apply, correction_eq_zero_of_fixed g.val.val x.1 hv, hv, add_zero]

lemma cover_fixed : fixed ((action (K := K)).comp (standard (K := K)).subtype) =
    (firstLine (K := K)).comap projection.toLinearMap := by
  rw [fixed_preimage, natural_fixed]

lemma firstLine_formD (x : Natural (K := K)) (hx : x ∈ firstLine) :
    ClassicalOrthogonal.formD 2 K x = 0 := by
  have hx' := point_le_plane (F := K) hx
  simp [ClassicalOrthogonal.formD_apply, hx' 0, hx' 1, Fin.sum_univ_two]

lemma firstLine_isotropic (x y : Natural (K := K)) (hx : x ∈ firstLine) (hy : y ∈ firstLine) :
    (ClassicalOrthogonal.formD 2 K).polarBilin x y = 0 := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    firstLine_formD _ hx, firstLine_formD _ hy,
    firstLine_formD _ (firstLine.add_mem hx hy), sub_zero]

lemma secondPlane_formD (x : Natural (K := K)) (hx : x ∈ secondPlane) :
    ClassicalOrthogonal.formD 2 K x = 0 := by
  have hx' := (secondPlane_eq_plane (K := K)) ▸ hx
  simp [ClassicalOrthogonal.formD_apply, hx' 0, hx' 1, Fin.sum_univ_two]

lemma secondPlane_isotropic (x y : Natural (K := K)) (hx : x ∈ secondPlane) (hy : y ∈ secondPlane) :
    (ClassicalOrthogonal.formD 2 K).polarBilin x y = 0 := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    secondPlane_formD _ hx, secondPlane_formD _ hy,
    secondPlane_formD _ (secondPlane.add_mem hx hy), sub_zero]

lemma singularPoint_singular (x : Space (K := K)) (hx : x ∈ singularPoint) :
    ClassicalOrthogonal.formB 2 K x = 0 := by
  have hx' : x.1 ∈ firstLine ∧ x.2 = 0 := hx
  rw [ClassicalOrthogonal.formB_apply, firstLine_formD _ hx'.1, hx'.2]
  simp

lemma singular_iff (x : Space (K := K)) (hx : projection x ∈ firstLine) :
    ClassicalOrthogonal.formB 2 K x = 0 ↔ x ∈ singularPoint := by
  change x.1 ∈ firstLine at hx
  rw [ClassicalOrthogonal.formB_apply, firstLine_formD _ hx, zero_add]
  change x.2 ^ 2 = 0 ↔ x.1 ∈ firstLine ∧ x.2 = 0
  rw [pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)]
  exact ⟨fun h => ⟨hx,h⟩, And.right⟩

lemma first_preimage_eq : (firstLine (K := K)).comap projection.toLinearMap =
    singularPoint ⊔ radical := by
  apply le_antisymm
  · intro x hx
    have hp : (x.1, (0 : K)) ∈ singularPoint (K := K) := ⟨hx,rfl⟩
    have hr : ((0 : Natural (K := K)), x.2) ∈ radical := rfl
    have hh := Submodule.add_mem (singularPoint ⊔ radical)
      (Submodule.mem_sup_left hp) (Submodule.mem_sup_right hr)
    simpa using hh
  · apply sup_le
    · intro x hx
      exact hx.1
    · intro x hx
      change x.1 ∈ firstLine
      rw [show x.1 = 0 from hx]
      exact Submodule.zero_mem _

lemma singularPoint_disjoint : Disjoint (singularPoint (K := K)) radical := by
  apply disjoint_iff.mpr
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  exact Prod.ext hx.2 hx.1.2

private def singularPointEquiv : singularPoint (K := K) ≃ₗ[K] firstLine (K := K) where
  toFun x := ⟨x.val.1, x.property.1⟩
  invFun x := ⟨(x.val,0), x.property,rfl⟩
  left_inv x := by apply Subtype.ext; exact Prod.ext rfl x.property.2.symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma singularPoint_finrank : Module.finrank K (singularPoint (K := K)) = 1 :=
  singularPointEquiv.finrank_eq.trans firstLine_finrank

lemma first_preimage_finrank :
    Module.finrank K ((firstLine (K := K)).comap projection.toLinearMap) = 2 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (singularPoint (K := K)) (radical (K := K))
  rw [singularPoint_disjoint.eq_bot, finrank_bot, add_zero,
    singularPoint_finrank, radical_finrank] at h
  rw [first_preimage_eq]
  exact h

lemma singular_unique (P : Submodule K (Space (K := K)))
    (hle : P ≤ (firstLine (K := K)).comap projection.toLinearMap)
    (hdim : Module.finrank K P = 1) (hq : ∀ x ∈ P, ClassicalOrthogonal.formB 2 K x = 0) :
    P = singularPoint := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx
    exact (singular_iff x (hle hx)).mp (hq x hx)
  · rw [hdim, singularPoint_finrank]

/-- The literal standard transvection root, intersected with the derived group. -/
def transvectionRoot : Subgroup (L (K := K)) :=
  (RootSubgroup.group (F := K) 0).subgroupOf (commutator (Sp K))

/-- Placement in the intrinsic center, retaining both original subgroup inclusions.
The statement includes the (trivial) binary root intersection. -/
lemma transvectionRoot_central : transvectionRoot (K := K) ≤
    (Subgroup.center (standard (K := K))).map (standard (K := K)).subtype := by
  intro x hx
  obtain ⟨t, ht⟩ := (RootSubgroup.mem_group_iff 0 x.val).mp hx
  have hxu : x.val ∈ unipotent := by
    rw [← ht]
    exact positive_root_mem_unipotent 0 t (by simp)
  refine ⟨⟨x,hxu⟩, ?_, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Subtype.ext
  apply Subtype.ext
  have hc := Subgroup.mem_center_iff.mp (CentralRootGeometry.theta_mem_center t (0 : K))
    ⟨y.val.val,y.property⟩
  have he : (CentralRootGeometry.theta t (0 : K)).val = x.val := by
    rw [CentralRootGeometry.theta_val, RootSubgroup.element_zero, mul_one, ht]
  simpa only [Subgroup.coe_mul, he] using congrArg Subtype.val hc

end Representation.SymplecticFourOrthogonalCover.SylowFlag
