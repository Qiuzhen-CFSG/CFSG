module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.Saturation
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.SpanImage
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.FamilyAction
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Models
public import Theory.SpecificGroups.BinaryLinear.FourParabolicRadical
public import Mathlib.Algebra.Module.ZMod

/-!
# Saturating the actual four-dimensional span action

For the binary plane stabilizer, surjectivity of the joint restriction/quotient
map gives P=P₀R. Its two factors have trivial two-core, so O₂(P₀) lies in R.
The existing explicit matrix proof identifies R with O₂(P), proves that R is
abelian, and proves its irreducibility under P. Hence a nontrivial O₂(P₀)
fills R and gives P₀=P. No normality of P₀ in P is assumed.

The source application conjugates the literal action on W=⟨V^Y⟩ through an
actual binary coordinate equivalence carrying V₂ to the marked plane. This
also proves that the group-automorphism stabilizer is the full linear plane
stabilizer; the comparison is not a group-family label.

Two source-specific premises remain: the JOINT block map must be surjective,
and the source image must have nontrivial two-core. They are not conclusions
of 14.7.55 as stated. Their producer must use the earlier I₂=L₂O₂(H) action
and the residual Y=O²(C_H(V₂)) acting on the literal lifted pencil. Separate
surjectivity onto the two factors cannot replace joint surjectivity. The
parent `qt-14-07-g2-local-parabolics` retains this discharge.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
14.7.56(2), printed p.1066. The reused binary matrix calculation is in
`Theory.SpecificGroups.BinaryLinear.FourParabolicRadical`.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.SpanSaturation

open Subgroup
open scoped Pointwise
open BinaryLinear BinaryLinear.SmallParabolicLevi
open BinaryLinear.FourParabolicRadical
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics


private theorem block_image_core_eq_bot {X : Type*} [Group X]
    (f : X →* (BinaryLinear.GL plane × BinaryLinear.GL (Space ⧸ plane))) (hf : Function.Surjective f) :
    (pCore 2 X).map f = ⊥ := by
  let a := (MonoidHom.fst (BinaryLinear.GL plane) (BinaryLinear.GL (Space ⧸ plane))).comp f
  let b := (MonoidHom.snd (BinaryLinear.GL plane) (BinaryLinear.GL (Space ⧸ plane))).comp f
  have ha : Function.Surjective a := fun x => by
    obtain ⟨y,hy⟩ := hf (x,1)
    exact ⟨y,congrArg Prod.fst hy⟩
  have hb : Function.Surjective b := fun x => by
    obtain ⟨y,hy⟩ := hf (1,x)
    exact ⟨y,congrArg Prod.snd hy⟩
  have hca : (pCore 2 X).map a ≤ pCore 2 (BinaryLinear.GL plane) :=
    le_sSup ⟨Normal.map inferInstance a ha,pCore_isPGroup.map a⟩
  have hcb : (pCore 2 X).map b ≤ pCore 2 (BinaryLinear.GL (Space ⧸ plane)) :=
    le_sSup ⟨Normal.map inferInstance b hb,pCore_isPGroup.map b⟩
  rw [linearGroup_twoCore_eq_bot] at hca hcb
  apply bot_unique
  rintro _ ⟨x,hx,rfl⟩
  exact Prod.ext (hca (mem_map_of_mem _ hx)) (hcb (mem_map_of_mem _ hx))

private theorem cover_of_joint_blocks (J : Subgroup Lin) (hJ : J ≤ parabolic plane)
    (hfull : Function.Surjective ((blockAction plane).comp (inclusion hJ))) :
    J ⊔ radical plane = parabolic plane := by
  apply le_antisymm (sup_le hJ (radical_le_parabolic _))
  intro g hg
  obtain ⟨j,hj⟩ := hfull (blockAction plane ⟨g,hg⟩)
  let k : parabolic plane := ⟨g,hg⟩ * (inclusion hJ j)⁻¹
  have hk : k ∈ (blockAction plane).ker := by
    change blockAction plane k = 1
    dsimp only [k]
    rw [map_mul,map_inv]
    change blockAction plane ⟨g,hg⟩ *
      (((blockAction plane).comp (inclusion hJ)) j)⁻¹ = 1
    rw [hj,mul_inv_cancel]
  rw [ker_blockAction] at hk
  have hm := (J ⊔ radical plane).mul_mem ((le_sup_right : radical plane ≤ J ⊔ radical plane) hk)
    ((le_sup_left : J ≤ J ⊔ radical plane) j.property)
  change (g * (j : Lin)⁻¹) * j ∈ J ⊔ radical plane at hm
  simpa only [inv_mul_cancel_right] using hm

private theorem core_le_radical_of_joint_blocks (J : Subgroup Lin) (hJ : J ≤ parabolic plane)
    (hfull : Function.Surjective ((blockAction plane).comp (inclusion hJ))) :
    J.pCoreIn 2 ≤ radical plane := by
  rintro _ ⟨j,hj,rfl⟩
  have he := block_image_core_eq_bot ((blockAction plane).comp (inclusion hJ)) hfull
  have hjk : inclusion hJ j ∈ (blockAction plane).ker := by
    have := mem_map_of_mem ((blockAction plane).comp (inclusion hJ)) hj
    rw [he] at this
    exact this
  rw [ker_blockAction] at hjk
  exact hjk

/-- The genuine binary plane stabilizer is filled by a subgroup with full
joint block image and a nontrivial two-core. -/
theorem binary_plane_saturation (J : Subgroup Lin) (hJ : J ≤ parabolic plane)
    (hfull : Function.Surjective ((blockAction plane).comp (inclusion hJ)))
    (hseed : J.pCoreIn 2 ≠ ⊥) : J = parabolic plane := by
  apply stabilizer_saturation J (radical plane) (parabolic plane) (J.pCoreIn 2)
    (cover_of_joint_blocks J hJ hfull) (core_le_radical_of_joint_blocks J hJ hfull)
    (pCoreIn_le 2 J) hseed
  · exact J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  · apply le_centralizer_iff_isMulCommutative.mpr
    rw [← range_upper]
    infer_instance
  · exact radical_irreducible

/-- Coordinates for the elementary abelian span of order sixteen. -/
abbrev BSpace := BinaryLinear.FourParabolicRadical.Space

/-- Actual conversion of binary automorphisms to linear maps. -/
def binaryAutEquiv : MulAut (Multiplicative BSpace) ≃* Lin where
  toFun a := { AddEquiv.toMultiplicative.symm a with
    map_smul' := ZMod.map_smul (AddEquiv.toMultiplicative.symm a) }
  invFun a := AddEquiv.toMultiplicative a.toAddEquiv
  left_inv a := by ext <;> rfl
  right_inv a := by ext <;> rfl
  map_mul' a b := by ext <;> rfl

variable {A : Type*} [Group A]

/-- Conjugate the actual automorphisms through the specified coordinates. -/
def autCoordinates (E : A ≃* Multiplicative BSpace) : MulAut A ≃* Lin :=
  (MulAut.congr E).trans binaryAutEquiv

/-- Coordinate change retains evaluation on each vector. -/
theorem autCoordinates_apply (E : A ≃* Multiplicative BSpace) (a : MulAut A) (x : BSpace) :
    autCoordinates E a x = (E (a (E.symm (.ofAdd x)))).toAdd := rfl

/-- The marked group stabilizer is exactly the binary linear parabolic. -/
theorem autCoordinates_parabolic (E : A ≃* Multiplicative BSpace) (D : Subgroup A)
    (hD : D.map E.toMonoidHom = plane.toAddSubgroup.toSubgroup)
    (a : MulAut A) :
    a ∈ MulAction.stabilizer (MulAut A) D ↔ autCoordinates E a ∈ parabolic plane := by
  have hmem (x : A) : x ∈ D ↔ (E x).toAdd ∈ plane := by
    change x ∈ D ↔ E x ∈ plane.toAddSubgroup.toSubgroup
    rw [← hD]
    simp only [mem_map_equiv, E.symm_apply_apply]
  rw [mem_automorphism_stabilizer_iff]
  change (∀ x, a x ∈ D ↔ x ∈ D) ↔
    ∀ v : BSpace, autCoordinates E a v ∈ plane ↔ v ∈ plane
  constructor
  · intro ha v
    rw [autCoordinates_apply, ← hmem,ha,hmem]
    rw [E.apply_symm_apply]
    rfl
  · intro ha x
    rw [hmem,hmem]
    have hv := ha (E x).toAdd
    change (E (a (E.symm (E x)))).toAdd ∈ plane ↔ (E x).toAdd ∈ plane at hv
    simpa only [E.symm_apply_apply] using hv

open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry
variable {G : Type*} [Group G]

/-- The literal conjugation action in coordinates preserving V₂. -/
def spanCoordinateAction (V V₂ Y : Subgroup G) (hV₂ : V₂ ≤ V)
    (hspan : normalizer (V₂ : Set G) ≤ normalizer (generatedLineFamily V Y : Set G))
    (E : generatedLineFamily V Y ≃* Multiplicative BSpace)
    (hE : (V₂.subgroupOf (generatedLineFamily V Y)).map E.toMonoidHom =
      plane.toAddSubgroup.toSubgroup) : normalizer (V₂ : Set G) →* parabolic plane :=
  ((autCoordinates E).toMonoidHom.comp (ambientAction _ _ hspan)).codRestrict _ (by
    intro g
    exact (autCoordinates_parabolic E _ hE _).mp
      (ambient_span_action_range_le_stabilizer V V₂ Y hV₂ hspan ⟨g,rfl⟩))

/-- Apply the checked binary radical calculation to the actual source span.
The remaining source-action branch must supply the two explicit hypotheses
`hfull` and `hseed`; neither is asserted to follow from unmarked factor images. -/
theorem source_full_span_image_of_joint_blocks (V V₂ Y : Subgroup G) (hV₂ : V₂ ≤ V)
    (hspan : normalizer (V₂ : Set G) ≤ normalizer (generatedLineFamily V Y : Set G))
    (E : generatedLineFamily V Y ≃* Multiplicative BSpace)
    (hE : (V₂.subgroupOf (generatedLineFamily V Y)).map E.toMonoidHom =
      plane.toAddSubgroup.toSubgroup)
    (hfull : Function.Surjective ((blockAction plane).comp
      (spanCoordinateAction V V₂ Y hV₂ hspan E hE)))
    (hseed : (((autCoordinates E).toMonoidHom.comp
      (ambientAction _ _ hspan)).range).pCoreIn 2 ≠ ⊥) :
    (ambientAction _ _ hspan).range = MulAction.stabilizer
      (MulAut (generatedLineFamily V Y)) (V₂.subgroupOf (generatedLineFamily V Y)) := by
  let f := (autCoordinates E).toMonoidHom.comp (ambientAction _ _ hspan)
  have hJ : f.range ≤ parabolic plane := by
    rintro _ ⟨g,rfl⟩
    exact (spanCoordinateAction V V₂ Y hV₂ hspan E hE g).property
  have hfull' : Function.Surjective ((blockAction plane).comp (inclusion hJ)) := by
    intro b
    obtain ⟨g,hg⟩ := hfull b
    exact ⟨⟨f g,⟨g,rfl⟩⟩,hg⟩
  have hsat := binary_plane_saturation f.range hJ hfull' hseed
  apply (map_injective (f := (autCoordinates E).toMonoidHom) (autCoordinates E).injective)
  have hr : (ambientAction _ _ hspan).range.map (autCoordinates E).toMonoidHom = f.range :=
    MonoidHom.range_comp _ _ |>.symm
  rw [hr,hsat]
  ext a
  rw [mem_map_equiv]
  have h := autCoordinates_parabolic E _ hE ((autCoordinates E).symm a)
  simpa only [MulEquiv.apply_symm_apply] using h.symm

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.SpanSaturation
