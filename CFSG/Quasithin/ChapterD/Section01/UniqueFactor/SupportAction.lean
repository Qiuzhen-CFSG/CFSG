module
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.Setup
public import Theory.Representation.BinaryOffender.InvariantAction

/-!
# The literal subgroup and subspace conjugation images

A binary subspace of a normal elementary subgroup determines an ambient
subgroup by inclusion. Restricting the original action to that subspace and
acting directly on the ambient subgroup have the same centralizer kernel.
The two actual quotient-to-image isomorphisms identify their action groups.
The inclusion also gives a linear equivalence, intertwining those two actions.

Source application: the proper chosen four-space in Aschbacher–Smith
15.1.4–6, printed p.1087.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.UniqueFactor
variable {G : Type*} [Group G]

/-- Both faithful action images are the quotient by the same actual centralizer. -/
noncomputable def supportActionEquiv (M V : Subgroup G)
    [IsElementaryAbelian 2 V] (hMV : M ≤ normalizer (V : Set G))
    (U : Submodule (ZMod 2) (Additive V))
    (hU : (⊤ : Subgroup (internalActionImage M V hMV)) ≤
      subspaceStabilizer (imageRepresentation M V hMV) U)
    (hMW : M ≤ normalizer (((Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype) : Set G)) :
    internalActionImage M ((Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype) hMW ≃*
      subspaceActionImage (imageRepresentation M V hMV) U := by
  let W := (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype
  let ρ := imageRepresentation M V hMV
  let f : M →* internalActionImage M W hMW := (actionHom M W hMW).rangeRestrict
  let q : M →* internalActionImage M V hMV := (actionHom M V hMV).rangeRestrict
  let k := (invariantActionHom ρ U hU).comp q
  have hk : Function.Surjective k := (invariantActionHom_surjective ρ U hU).comp
    (actionHom M V hMV).rangeRestrict_surjective
  have he : f.ker = k.ker := by
    change (actionHom M W hMW).rangeRestrict.ker =
      ((invariantActionHom ρ U hU).comp q).ker
    rw [MonoidHom.ker_rangeRestrict,actionHom_ker,← MonoidHom.comap_ker,invariantActionHom_ker]
    ext m
    constructor
    · intro hm
      refine ⟨mem_top _,?_⟩
      intro w hw
      have he := hm (w.toMul : G) (mem_map_of_mem V.subtype hw)
      apply Additive.toMul.injective
      apply Subtype.ext
      change (m : G) * (w.toMul : G) * (m : G)⁻¹ = w.toMul
      change (w.toMul : G) * (m : G) = (m : G) * (w.toMul : G) at he
      rw [←he,mul_inv_cancel_right]
    · rintro ⟨_,hm⟩ v ⟨w,hw,rfl⟩
      have he := congrArg (fun y : Additive V => (y.toMul : G))
        (hm (Additive.ofMul w) hw)
      change (m:G) * (w:G) * (m:G)⁻¹ = (w:G) at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
  exact (QuotientGroup.quotientKerEquivOfSurjective f
    (actionHom M W hMW).rangeRestrict_surjective).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq he).trans
        (QuotientGroup.quotientKerEquivOfSurjective k hk))


private theorem quotient_symm_apply {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hf : Function.Surjective f) (x : X) :
    (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f x) =
      QuotientGroup.mk x := by
  apply (QuotientGroup.quotientKerEquivOfSurjective f hf).injective
  rw [MulEquiv.apply_symm_apply]
  rfl

private theorem quotient_identification_apply {X Y Z : Type*} [Group X] [Group Y] [Group Z]
    (f : X →* Y) (k : X →* Z) (hf : Function.Surjective f) (hk : Function.Surjective k)
    (he : f.ker = k.ker) (x : X) :
    ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq he).trans
        (QuotientGroup.quotientKerEquivOfSurjective k hk))) (f x) = k x := by
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, quotient_symm_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- The support-image identification preserves the action of each original actor. -/
theorem supportActionEquiv_apply (M V : Subgroup G)
    [IsElementaryAbelian 2 V] (hMV : M ≤ normalizer (V : Set G))
    (U : Submodule (ZMod 2) (Additive V))
    (hU : (⊤ : Subgroup (internalActionImage M V hMV)) ≤
      subspaceStabilizer (imageRepresentation M V hMV) U)
    (hMW : M ≤ normalizer (((Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype) : Set G))
    (m : M) :
    supportActionEquiv M V hMV U hU hMW ((actionHom M _ hMW).rangeRestrict m) =
      invariantActionHom (imageRepresentation M V hMV) U hU
        ((actionHom M V hMV).rangeRestrict m) := by
  unfold supportActionEquiv
  exact quotient_identification_apply _ _ _ _ _ m

/-- Inclusion identifies the original subspace with the literal ambient subgroup. -/
noncomputable def supportLinearEquiv (V : Subgroup G) [IsElementaryAbelian 2 V]
    (U : Submodule (ZMod 2) (Additive V))
    [IsElementaryAbelian 2 ((Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype)] :
    U ≃ₗ[ZMod 2] Additive ((Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype) := by
  let f : U →+ Additive ((Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype) :=
    { toFun := fun u => Additive.ofMul ⟨u.val.toMul.val, mem_map_of_mem V.subtype u.property⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  apply LinearEquiv.ofBijective (f.toZModLinearMap 2)
  constructor
  · intro u v huv
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun w => w.toMul.val) huv
  · intro w
    obtain ⟨v,hv,hvw⟩ := w.toMul.property
    refine ⟨⟨Additive.ofMul v,hv⟩,?_⟩
    apply Additive.toMul.injective
    exact Subtype.ext hvw

/-- The two linear actions agree under inclusion of the actual support. -/
theorem supportActionEquiv_intertwines (M V : Subgroup G)
    [IsElementaryAbelian 2 V] (hMV : M ≤ normalizer (V : Set G))
    (U : Submodule (ZMod 2) (Additive V))
    [IsElementaryAbelian 2 ((Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype)]
    (hU : (⊤ : Subgroup (internalActionImage M V hMV)) ≤
      subspaceStabilizer (imageRepresentation M V hMV) U)
    (hMW : M ≤ normalizer (((Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype) : Set G))
    (g : internalActionImage M ((Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype) hMW)
    (u : U) :
    supportLinearEquiv V U (subspaceImageRepresentation (imageRepresentation M V hMV) U
      (supportActionEquiv M V hMV U hU hMW g) u) =
        imageRepresentation M _ hMW g (supportLinearEquiv V U u) := by
  obtain ⟨m,rfl⟩ := (actionHom M _ hMW).rangeRestrict_surjective g
  rw [supportActionEquiv_apply]
  rfl

/-- Restriction of actual conjugation is equivariant in the reverse coordinates. -/
theorem supportActionEquiv_intertwines_symm (M V : Subgroup G)
    [IsElementaryAbelian 2 V] (hMV : M ≤ normalizer (V : Set G))
    (U : Submodule (ZMod 2) (Additive V))
    [IsElementaryAbelian 2 ((Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype)]
    (hU : (⊤ : Subgroup (internalActionImage M V hMV)) ≤
      subspaceStabilizer (imageRepresentation M V hMV) U)
    (hMW : M ≤ normalizer (((Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype) : Set G))
    (g : internalActionImage M ((Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype) hMW)
    (w : Additive ((Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype)) :
    (supportLinearEquiv V U).symm (imageRepresentation M _ hMW g w) =
      subspaceImageRepresentation (imageRepresentation M V hMV) U
        (supportActionEquiv M V hMV U hU hMW g) ((supportLinearEquiv V U).symm w) := by
  apply (supportLinearEquiv V U).injective
  rw [LinearEquiv.apply_symm_apply, supportActionEquiv_intertwines,
    LinearEquiv.apply_symm_apply]

end CFSG.Quasithin.ChapterD.UniqueFactor
