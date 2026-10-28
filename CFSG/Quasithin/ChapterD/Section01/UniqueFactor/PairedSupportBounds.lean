module
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SupportAction
public import Theory.Representation.BinaryOffender.SpanningPair

/-!
# Sharp offender bounds on original subgroup supports

Conjugation transports both the actor and its elementary module, preserving
the literal action and every offender ratio. Two invariant subgroups spanning
an elementary module then transfer their sharp bounds to its faithful action
image. The proof identifies the subgroup and subspace action images through
their identical centralizer kernels and applies the spanning-pair inequality;
it does not require the two subgroups to intersect trivially.

Source application: the positive central covers in Aschbacher--Smith 10.2.8,
printed p.749; the restriction inequality is B.7.1, pp.118--119.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Conjugating both the actor and the module preserves the sharp offender bound. -/
theorem conjugate_image_not_strong (H V : Subgroup G) [IsElementaryAbelian 2 V]
    (hHV : H ≤ normalizer (V : Set G)) (f : MulAut G)
    (hN : H.map f.toMonoidHom ≤ normalizer (V.map f.toMonoidHom : Set G))
    (hn : ¬ IsStrongFFModule (imageRepresentation H V hHV)) :
    letI : IsElementaryAbelian 2 (V.map f.toMonoidHom) := IsElementaryAbelian.map _
    ¬ IsStrongFFModule (imageRepresentation (H.map f.toMonoidHom) (V.map f.toMonoidHom) hN) := by
  let : IsElementaryAbelian 2 (V.map f.toMonoidHom) := IsElementaryAbelian.map _
  let e : V ≃* V.map f.toMonoidHom := V.equivMapOfInjective f.toMonoidHom f.injective
  let E : Additive V ≃ₗ[ZMod 2] Additive (V.map f.toMonoidHom) :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
  let τ := imageRepresentation H V hHV
  let σ := imageRepresentation (H.map f.toMonoidHom) (V.map f.toMonoidHom) hN
  have hmem (a : internalActionImage (H.map f.toMonoidHom) (V.map f.toMonoidHom) hN) :
      MulAut.congr e.symm a.val ∈ internalActionImage H V hHV := by
    obtain ⟨n,hn⟩ := a.property
    obtain ⟨m,hm,he⟩ := n.property
    refine ⟨⟨m,hm⟩,?_⟩
    apply MulEquiv.ext
    intro v
    apply e.injective
    apply Subtype.ext
    change f (m*(v : G)*m⁻¹) = _
    have ha : (a.val (e v) : G) = (n : G) * (e v : G) * (n : G)⁻¹ := by
      rw [←hn]
      rfl
    change f (m*(v : G)*m⁻¹) = (e (e.symm (a.val (e v))) : G)
    rw [e.apply_symm_apply,ha,←he]
    exact map_mul f _ _ |>.trans (by rw [map_mul,map_inv]; rfl)
  let i : internalActionImage (H.map f.toMonoidHom) (V.map f.toMonoidHom) hN →*
      internalActionImage H V hHV :=
    ((MulAut.congr e.symm).toMonoidHom.comp
      (internalActionImage (H.map f.toMonoidHom) (V.map f.toMonoidHom) hN).subtype).codRestrict _ hmem
  have hi : Function.Injective i := by
    intro a b hab
    apply Subtype.ext
    exact (MulAut.congr e.symm).injective (congrArg Subtype.val hab)
  apply not_strong_of_equivariant σ τ i hi E.symm _ hn
  intro a v
  apply E.injective
  rw [E.apply_symm_apply]
  apply Additive.toMul.injective
  change a.val v.toMul = e (e.symm (a.val (e (E.symm v).toMul)))
  rw [e.apply_symm_apply]
  exact congrArg a.val (congrArg Additive.toMul (E.apply_symm_apply v)).symm

/-- Two invariant original subgroups spanning V transfer their sharp action
bounds to the actual conjugation image on V; their intersection may be nontrivial. -/
theorem spanning_pair_image_not_strong (H V W U : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 U]
    (hHV : H ≤ normalizer (V : Set G))
    (hHW : H ≤ normalizer (W : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hgen : W ⊔ U = V)
    (hnW : ¬ IsStrongFFModule (imageRepresentation H W hHW))
    (hnU : ¬ IsStrongFFModule (imageRepresentation H U hHU)) :
    ¬ IsStrongFFModule (imageRepresentation H V hHV) := by
  let ρ := imageRepresentation H V hHV
  let X : Submodule (ZMod 2) (Additive V) := AddSubgroup.toZModSubmodule 2 (W.subgroupOf V).toAddSubgroup
  let Y : Submodule (ZMod 2) (Additive V) := AddSubgroup.toZModSubmodule 2 (U.subgroupOf V).toAddSubgroup
  have hWV : W ≤ V := hgen ▸ le_sup_left
  have hUV : U ≤ V := hgen ▸ le_sup_right
  have hspan : X ⊔ Y=⊤ := by
    apply top_unique
    intro v _
    have hv : (v.toMul : G) ∈ W ⊔ U := hgen ▸ v.toMul.property
    have hWU : W ≤ normalizer (U : Set G) :=
      (hWV.trans (V.le_centralizer.trans (centralizer_le hUV))).trans (centralizer_le_normalizer _)
    have hv' : (v.toMul : G) ∈ (W : Set G) * (U : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right W U hWU]
      exact hv
    obtain ⟨w,hw,u,hu,he⟩ := hv'
    exact Submodule.mem_sup.mpr ⟨Additive.ofMul ⟨w,hWV hw⟩,hw,
      Additive.ofMul ⟨u,hUV hu⟩,hu,congrArg Additive.ofMul (Subtype.ext he)⟩
  have hstable (Z : Subgroup G) (hZ : H ≤ normalizer (Z : Set G)) :
      (⊤ : Subgroup (internalActionImage H V hHV)) ≤
        subspaceStabilizer ρ (AddSubgroup.toZModSubmodule 2 (Z.subgroupOf V).toAddSubgroup) := by
    apply le_subspaceStabilizer
    intro a _ v hv
    obtain ⟨n,hn⟩ := a.property
    change (a.val v.toMul : G) ∈ Z
    rw [←hn]
    exact (mem_normalizer_iff.mp (hZ n.property) (v.toMul : G)).mp hv
  have hbound (Z : Subgroup G) [IsElementaryAbelian 2 Z]
      (hZ : H ≤ normalizer (Z : Set G)) (hZV : Z ≤ V)
      (hn : ¬ IsStrongFFModule (imageRepresentation H Z hZ)) :
      ¬ IsStrongFFModule (subspaceImageRepresentation ρ
        (AddSubgroup.toZModSubmodule 2 (Z.subgroupOf V).toAddSubgroup)) := by
    let P : Submodule (ZMod 2) (Additive V) := AddSubgroup.toZModSubmodule 2 (Z.subgroupOf V).toAddSubgroup
    have he : (Subgroup.toAddSubgroup.symm P.toAddSubgroup).map V.subtype=Z :=
      map_subgroupOf_eq_of_le hZV
    have hP : H ≤ normalizer ((Subgroup.toAddSubgroup.symm P.toAddSubgroup).map V.subtype : Set G) := he ▸ hZ
    let : IsElementaryAbelian 2 ((Subgroup.toAddSubgroup.symm P.toAddSubgroup).map V.subtype) := he ▸ inferInstance
    have hnP : ¬ IsStrongFFModule (imageRepresentation H
        ((Subgroup.toAddSubgroup.symm P.toAddSubgroup).map V.subtype) hP) := by
      have aux (Q : Subgroup G) [IsElementaryAbelian 2 Q] (hQ : Q=Z)
          (hHQ : H ≤ normalizer (Q : Set G)) :
          ¬ IsStrongFFModule (imageRepresentation H Q hHQ) := by
        cases hQ
        exact hn
      exact aux _ he hP
    let a := supportActionEquiv H V hHV P (hstable Z hZ) hP
    let b := supportLinearEquiv V P
    apply not_strong_of_equivariant _ _ a.symm.toMonoidHom a.symm.injective b _ hnP
    intro g v
    have hh := supportActionEquiv_intertwines H V hHV P (hstable Z hZ) hP (a.symm g) v
    change b (subspaceImageRepresentation ρ P (a (a.symm g)) v) = _ at hh
    rw [a.apply_symm_apply] at hh
    exact hh
  exact pair_not_strong ρ (imageRepresentation_injective H V hHV) X Y hspan
    (hstable W hHW) (hstable U hHU) (hbound W hHW hWV hnW) (hbound U hHU hUV hnU)
end CFSG.Quasithin.ChapterD.UniqueFactor
