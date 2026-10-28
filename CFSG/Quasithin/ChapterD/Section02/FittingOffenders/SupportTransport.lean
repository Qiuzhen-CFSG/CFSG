module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.GlobalTransport
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# Transporting literal marked support factors across equivariant coordinates

An injective group homomorphism and an equivariant linear equivalence carry
the order-three factors, their multiplication bijection, their two-dimensional
moved planes, and their addition bijection to the actual image actor. This is
the coordinate transport needed when a D.2.17 factor is identified with an
M-normal component of V(M) in original 15.1.2, printed p.1085.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
variable {G H V W : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) H W)

noncomputable def SupportFactors.map {P : Subgroup G} {s : ℕ}
    (d : SupportFactors ρ P s) (f : G →* H) (hf : Function.Injective f)
    (e : V ≃ₗ[ZMod 2] W) (he : ∀ g v, e (ρ g v) = σ (f g) (e v)) :
    SupportFactors σ (P.map f) s := by
  classical
  let ep : P ≃* P.map f := MulEquiv.ofBijective (f.subgroupMap P)
    ⟨fun x y h => Subtype.ext (hf (congrArg Subtype.val h)),f.subgroupMap_surjective P⟩
  let F (i : Fin s) : Subgroup (P.map f) := (d.factor i).map ep.toMonoidHom
  have hF (i : Fin s) : (F i).map (P.map f).subtype = (d.ambient i).map f := by
    simp only [F, SupportFactors.ambient, map_map]
    congr 1
  have hmove (B : Subgroup G) :
      (subspaceCommutator ρ ⊤ B).map e.toLinearMap = subspaceCommutator σ ⊤ (B.map f) := by
    have hh := subspaceCommutator_map_embedding (σ.comp f) ρ (MonoidHom.id G)
      e.toLinearMap (fun g v => (he g v).symm) B ⊤
    simpa only [Submodule.map_top,LinearEquiv.range,Subgroup.map_id,
      subspaceCommutator_comp_map] using hh.symm
  have hU (i : Fin s) : (subspaceCommutator ρ ⊤ (d.ambient i)).map e.toLinearMap =
      subspaceCommutator σ ⊤ ((F i).map (P.map f).subtype) := by rw [hF,hmove]
  let E (i : Fin s) : subspaceCommutator ρ ⊤ (d.ambient i) ≃ₗ[ZMod 2]
      subspaceCommutator σ ⊤ ((F i).map (P.map f).subtype) :=
    (Submodule.equivMapOfInjective e.toLinearMap e.injective _).trans
      (LinearEquiv.ofEq _ _ (hU i))
  refine ⟨F,?_,?_,?_,?_⟩
  · intro i
    exact (Nat.card_congr (ep.subgroupMap (d.factor i)).toEquiv).symm.trans (d.card_factor i)
  · let E : ((i : Fin s) → F i) ≃ ((i : Fin s) → d.factor i) :=
      Equiv.piCongrRight fun i => (ep.subgroupMap (d.factor i)).symm.toEquiv
    have hb := ep.bijective.comp (d.multiply_bijective.comp E.bijective)
    convert hb using 1
    funext x
    simp only [Function.comp_apply,map_list_prod,List.map_ofFn]
    congr 1
    apply congrArg List.ofFn
    funext i
    exact (congrArg Subtype.val ((ep.subgroupMap (d.factor i)).apply_symm_apply (x i))).symm
  · intro i
    exact (E i).finrank_eq.symm.trans (d.support_dim i)
  · let Eall : ((i : Fin s) → subspaceCommutator σ ⊤ ((F i).map (P.map f).subtype)) ≃
        ((i : Fin s) → subspaceCommutator ρ ⊤ (d.ambient i)) :=
      Equiv.piCongrRight fun i => (E i).symm.toEquiv
    have hb := e.bijective.comp (d.add_bijective.comp Eall.bijective)
    convert hb using 1
    funext x
    change (∑ i, (x i : W)) = e (∑ i, ((E i).symm (x i) : V))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hh := congrArg Subtype.val ((E i).apply_symm_apply (x i))
    exact hh.symm
end CFSG.Quasithin.ChapterD.FittingConfigurations
