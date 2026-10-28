module
public import Theory.GroupTheory.ReducedNormal.SubspaceEquiv
public import Mathlib.RepresentationTheory.Intertwining

/-!
# The original orbit image and its literal group quotient

For an invariant reduced-normal subspace W with actual subgroup image U,
the projection onto U/C_U(X) has kernel W ∩ C_{R₂(H)}(X). The first
isomorphism theorem and the canonical central-image equivalence therefore
identify its actual image in R₂(H)/C_{R₂(H)}(X) with U/C_U(X). The
representative formula retains the original ambient vector and action.

Source: Aschbacher–Smith, 3.2.2(3), printed p.579, and D.3.4(3), p.193.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace Theory.GroupTheory.ReducedNormal
variable {G : Type*} [Group G]

/-- The literal centralizer quotient and the original ambient central image
are equivariantly isomorphic through their original projection. -/
theorem exists_actual_central_image_equiv
    (H : Subgroup G) (W : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup H)))
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (ReducedNormal.representation H) W)
    (X : Subgroup G) (hX : X ≤ H)
    (U : Subgroup G) [IsElementaryAbelian 2 U]
    (hU : ReducedNormal.subspaceImage H W = U)
    (hnU : H ≤ normalizer (U : Set G))
    (σ : Representation (ZMod 2) H (Additive (U ⧸ (centralizer (X : Set G)).subgroupOf U)))
    (hσ : ∀ (g : H) (u : U),
      σ g (Additive.ofMul (QuotientGroup.mk' ((centralizer (X : Set G)).subgroupOf U) u)) =
        Additive.ofMul (QuotientGroup.mk' ((centralizer (X : Set G)).subgroupOf U)
          ⟨(g : G) * (u : G) * (g : G)⁻¹,
            (mem_normalizer_iff.mp (hnU g.property) u).mp u.property⟩)) :
    ∃ a : (quotientImage (ReducedNormal.representation H) (X.subgroupOf H) W
        (le_top.trans hW)).toRepresentation.Equiv
        (σ.comp (X.subgroupOf H).subtype),
      ∀ w : W,
        a ⟨(fixedSpace (ReducedNormal.representation H) (X.subgroupOf H)).mkQ w.val,
          ⟨w.val,w.property,rfl⟩⟩ =
            Additive.ofMul (QuotientGroup.mk' ((centralizer (X : Set G)).subgroupOf U)
              ⟨w.val.toMul.val.val,hU ▸
                (show w.val.toMul.val.val ∈ ReducedNormal.subspaceImage H W from
                  mem_map_of_mem _ (mem_map_of_mem _ w.property))⟩) := by
  subst U
  let ρ := ReducedNormal.representation H
  let Y := X.subgroupOf H
  let f := (ReducedNormal.centralizerProjection H W X).comp
    (ReducedNormal.subspaceEquiv H W).toLinearMap
  have hf : Function.Surjective f :=
    (ReducedNormal.centralizerProjection_surjective H W X).comp
      (ReducedNormal.subspaceEquiv H W).surjective
  have hk : f.ker = (fixedSpace ρ Y).comap W.subtype := by
    ext w
    rw [LinearMap.mem_ker]
    change QuotientGroup.mk' _ (ReducedNormal.subspaceEquiv H W w).toMul = 1 ↔ _
    constructor
    · intro hq x
      have hw := (QuotientGroup.eq_one_iff (ReducedNormal.subspaceEquiv H W w).toMul).mp hq
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      change (x.val.val : G) * w.val.toMul.val.val * (x.val.val : G)⁻¹ = w.val.toMul.val.val
      have he := hw x.val.val x.property
      change (x.val.val : G) * w.val.toMul.val.val = w.val.toMul.val.val * (x.val.val : G) at he
      rw [he,mul_inv_cancel_right]
    · intro hw
      apply (QuotientGroup.eq_one_iff _).mpr
      intro x hx
      have he := congrArg (fun v : Additive (ReducedNormal.ModuleGroup H) => v.toMul.val.val)
        (hw ⟨⟨x,hX hx⟩,hx⟩)
      change x * w.val.toMul.val.val * x⁻¹ = w.val.toMul.val.val at he
      exact mul_inv_eq_iff_eq_mul.mp he
  let b : centralQuotient ρ Y W ≃ₗ[ZMod 2]
      Additive ((ReducedNormal.subspaceImage H W) ⧸
        (centralizer (X : Set G)).subgroupOf (ReducedNormal.subspaceImage H W)) :=
    (Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hf)
  have hb (w : W) : b (Submodule.Quotient.mk w) = f w := rfl
  let a := (centralQuotientImageEquiv ρ Y W).symm.trans b
  have ha (w : W) : a ⟨(fixedSpace ρ Y).mkQ w.val,⟨w.val,w.property,rfl⟩⟩ = f w := by
    change b ((centralQuotientImageEquiv ρ Y W).symm
      ((centralQuotientImageEquiv ρ Y W) (Submodule.Quotient.mk w))) = f w
    rw [LinearEquiv.symm_apply_apply,hb]
  refine ⟨Representation.Equiv.mk a ?_,?_⟩
  · intro x
    apply LinearMap.ext
    intro v
    obtain ⟨w,hw,hv⟩ := v.property
    have hv' : v = ⟨(fixedSpace ρ Y).mkQ w,⟨w,hw,rfl⟩⟩ := Subtype.ext hv.symm
    subst v
    change a ⟨(fixedSpace ρ Y).mkQ (ρ x w),_⟩ =
      σ x.val (a ⟨(fixedSpace ρ Y).mkQ w,_⟩)
    have hleft := ha ⟨ρ x w,(hW (mem_top x.val) w).mpr hw⟩
    have hright := ha ⟨w,hw⟩
    exact hleft.trans ((hσ x.val (ReducedNormal.subspaceEquiv H W ⟨w,hw⟩)).symm.trans
      (congrArg (σ x.val) hright.symm))
  · intro w
    exact ha w

end Theory.GroupTheory.ReducedNormal
