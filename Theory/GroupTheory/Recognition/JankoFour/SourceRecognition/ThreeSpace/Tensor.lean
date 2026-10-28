module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.DualHom
public import Mathlib.LinearAlgebra.Contraction

/-!
# The marked dual-natural tensor factor

The contragredient Hom equivalence identifies the actual radical quotient
with Hom(Z,W). Contraction against the original marked basis converts this
to the binary linear equivalence R/Z(R) ≃ Z* ⊗ W. Precomposition by the
inverse action on Z gives the dual factor; postcomposition by the original
S/R action gives the second factor. We prove the tensor identity for the
literal quotient actions, the full normalizer quotient, and the SAME
Aut(Z) × S₅ marking used in the preceding construction.

The four-space W is the original pair-core section, not a newly chosen
representation. Its identification with the natural L₂(4) module still
requires the final module discriminator in the source proof of (4.4).

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (4.4), pp.597–598, DOI 10.1007/BF01232280.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative TensorProduct
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

/-- Every automorphism of an elementary binary group is linear over the prime field. -/
def binaryLinearAut {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (a : MulAut V) : Additive V ≃ₗ[ZMod 2] Additive V :=
  a.toAdditive.toLinearEquiv (ZMod.map_smul a.toAdditive)

@[simp] theorem binaryLinearAut_apply {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (a : MulAut V) (v : Additive V) :
    binaryLinearAut a v = Additive.ofMul (a v.toMul) := rfl

private def homLinearEquiv {V Z W : Type*} [Group V] [Group Z] [Group W]
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 Z] [IsElementaryAbelian 2 W]
    (F : V ≃* (Z →* W)) :
    Additive V ≃ₗ[ZMod 2] (Additive Z →ₗ[ZMod 2] Additive W) := by
  let E : Additive V ≃+ (Additive Z →ₗ[ZMod 2] Additive W) := {
    toFun v := (F v.toMul).toAdditive.toZModLinearMap 2
    invFun f := Additive.ofMul (F.symm (MonoidHom.toAdditive.symm f.toAddMonoidHom))
    left_inv v := by
      change Additive.ofMul (F.symm (F v.toMul)) = v
      simp
    right_inv f := by
      apply LinearMap.ext
      intro z
      change Additive.ofMul ((F (F.symm (MonoidHom.toAdditive.symm f.toAddMonoidHom))) z.toMul) = f z
      rw [F.apply_symm_apply]
      rfl
    map_add' u v := by
      apply LinearMap.ext
      intro z
      change Additive.ofMul ((F (u.toMul*v.toMul)) z.toMul) = _
      rw [map_mul]
      rfl }
  exact E.toLinearEquiv (ZMod.map_smul E)

private theorem tensorHom_congr {Z W : Type*} [AddCommGroup Z] [AddCommGroup W]
    [Module (ZMod 2) Z] [Module (ZMod 2) W]
    (a : Z ≃ₗ[ZMod 2] Z) (b : W ≃ₗ[ZMod 2] W)
    (q : Module.Dual (ZMod 2) Z ⊗[ZMod 2] W) (t : Z) :
    dualTensorHom (ZMod 2) Z W (TensorProduct.congr a.symm.dualMap b q) t =
      b (dualTensorHom (ZMod 2) Z W q (a.symm t)) := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul φ w => simp [dualTensorHom_apply]
  | add u v hu hv => simp [hu,hv]

namespace ThreeSpaceData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
variable (d : ThreeSpaceData z e X)
local instance : IsElementaryAbelian 2 d.space := d.elementary
attribute [local instance] R_normal_in_K R_normal_in_S_intrinsic R_normal_in_normalizer

/-- The tensor product on the dual of the original three-space and the original four-space. -/
theorem exists_radical_tensor_equiv (h : IsTypeJ4 z) :
    letI := d.R_center_quotient_elementary h
    letI := d.multiplicitySpace_elementary h
    ∃ F : Additive (d.R ⧸ center d.R) ≃ₗ[ZMod 2]
        Module.Dual (ZMod 2) (Additive d.space) ⊗[ZMod 2] Additive d.multiplicitySpace,
      ∀ a : d.K ⧸ d.R.subgroupOf d.K, ∀ b : d.S ⧸ d.R.subgroupOf d.S,
        ∀ v : Additive (d.R ⧸ center d.R),
      F (Additive.ofMul (d.KRadicalAction h a (d.SRadicalAction h b v.toMul))) =
        TensorProduct.congr (binaryLinearAut (d.KQuotientEquivAut h a)).symm.dualMap
          (binaryLinearAut (d.multiplicityAction h b)) (F v) := by
  let := d.R_center_quotient_elementary h
  let := d.multiplicitySpace_elementary h
  obtain ⟨E,hK,hS⟩ := d.exists_radical_hom_equiv h
  let L := homLinearEquiv E
  let B := (Pi.basisFun (ZMod 2) (Fin 3)).map d.markedCoordinates
  let C := dualTensorHomEquivOfBasis (N := Additive d.multiplicitySpace) B
  let F := L.trans C.symm
  have hCF (v : Additive (d.R ⧸ center d.R)) : C (F v) = L v := by
    exact C.apply_symm_apply (L v)
  refine ⟨F,?_⟩
  intro a b v
  apply C.injective
  rw [hCF]
  apply LinearMap.ext
  intro t
  change Additive.ofMul (E (d.KRadicalAction h a (d.SRadicalAction h b v.toMul)) t.toMul) =
    dualTensorHom (ZMod 2) (Additive d.space) (Additive d.multiplicitySpace)
      (TensorProduct.congr (binaryLinearAut (d.KQuotientEquivAut h a)).symm.dualMap
        (binaryLinearAut (d.multiplicityAction h b)) (F v)) t
  rw [tensorHom_congr]
  have hF_eval (t : Additive d.space) :
      dualTensorHom (ZMod 2) (Additive d.space) (Additive d.multiplicitySpace) (F v) t =
        Additive.ofMul (E v.toMul t.toMul) := by
    exact congrArg (fun l : Additive d.space →ₗ[ZMod 2] Additive d.multiplicitySpace => l t) (hCF v)
  rw [hF_eval,binaryLinearAut_apply]
  apply Additive.ofMul.injective
  have hmark : d.linearRadicalAction h (d.KQuotientEquivAut h a) = d.KRadicalAction h a := by
    change d.KRadicalAction h ((d.KQuotientEquivAut h).symm (d.KQuotientEquivAut h a)) = _
    rw [MulEquiv.symm_apply_apply]
  have hh := hK (d.KQuotientEquivAut h a) (d.SRadicalAction h b v.toMul)
    ((d.KQuotientEquivAut h a).symm t.toMul)
  rw [hmark,MulEquiv.apply_symm_apply,hS] at hh
  exact hh

/-- The same tensor equivalence intertwines the full normalizer quotient and both original factor markings. -/
theorem exists_radical_normalizer_tensor_equiv (h : IsTypeJ4 z) :
    letI := d.R_center_quotient_elementary h
    letI := d.multiplicitySpace_elementary h
    ∃ F : Additive (d.R ⧸ center d.R) ≃ₗ[ZMod 2]
        Module.Dual (ZMod 2) (Additive d.space) ⊗[ZMod 2] Additive d.multiplicitySpace,
      ∀ n : normalizer (d.space : Set G) ⧸ d.R.subgroupOf (normalizer (d.space : Set G)),
        ∀ v : Additive (d.R ⧸ center d.R),
      F (Additive.ofMul (d.radicalQuotientAction h n v.toMul)) =
        TensorProduct.congr
          (binaryLinearAut (d.markedNormalizerQuotientEquiv h n).1).symm.dualMap
          (binaryLinearAut (d.markedMultiplicityAction h (d.markedNormalizerQuotientEquiv h n).2))
          (F v) := by
  let := d.R_center_quotient_elementary h
  let := d.multiplicitySpace_elementary h
  obtain ⟨F,hF⟩ := d.exists_radical_tensor_equiv h
  refine ⟨F,?_⟩
  intro n v
  obtain ⟨⟨a,b⟩,rfl⟩ := (d.quotientProductEquiv h).surjective n
  have hm : d.markedNormalizerQuotientEquiv h (d.quotientProductEquiv h (a,b)) =
      (d.KQuotientEquivAut h a,d.SQuotientEquiv h b) := by
    change ((d.KQuotientEquivAut h).prodCongr (d.SQuotientEquiv h))
      ((d.quotientProductEquiv h).symm (d.quotientProductEquiv h (a,b))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  rw [hm,d.radical_product_action,MulAut.mul_apply]
  simpa only [d.markedMultiplicityAction_quotient] using hF a b v

/-- In the original S₅ marking, the action is the tensor of the dual action on Z and the same action on W. -/
theorem exists_radical_marked_tensor_equiv (h : IsTypeJ4 z) :
    letI := d.R_center_quotient_elementary h
    letI := d.multiplicitySpace_elementary h
    ∃ F : Additive (d.R ⧸ center d.R) ≃ₗ[ZMod 2]
        Module.Dual (ZMod 2) (Additive d.space) ⊗[ZMod 2] Additive d.multiplicitySpace,
      ∀ a : MulAut d.space, ∀ b : Equiv.Perm (Fin 5),
        ∀ v : Additive (d.R ⧸ center d.R),
      F (Additive.ofMul (d.markedRadicalAction h (a,b) v.toMul)) =
        TensorProduct.congr (binaryLinearAut a).symm.dualMap
          (binaryLinearAut (d.markedMultiplicityAction h b)) (F v) := by
  let := d.R_center_quotient_elementary h
  let := d.multiplicitySpace_elementary h
  obtain ⟨F,hF⟩ := d.exists_radical_normalizer_tensor_equiv h
  refine ⟨F,?_⟩
  intro a b v
  change F (Additive.ofMul ((d.radicalQuotientAction h)
    ((d.markedNormalizerQuotientEquiv h).symm (a,b)) v.toMul)) = _
  simpa only [MulEquiv.apply_symm_apply] using
    hF ((d.markedNormalizerQuotientEquiv h).symm (a,b)) v

end ThreeSpaceData
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
