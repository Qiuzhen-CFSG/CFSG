module

public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.Setup
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.GroupTheory.CentralizerQuotientNormalizer

/-!
# The literal chosen-module actor and its commutator

The actor is the image of D in the same conjugation range as the chosen
representation. Quadraticity passes from the orbit span to this image.
Coordinates identify the order of the ambient [V,D] with the dimension of
its linear moved space. An abelian image of T normalizes [V,D], by lifting
normalization through the genuine centralizer quotient.

These are the action transports used in Aschbacher--Smith 15.2.10--11,
printed pp.1110--1111 (combined manuscript, 1 March 2004).
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor

namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
variable {G : Type*} [Group G]

@[expose] noncomputable def actor (M V D : Subgroup G) (hn : M ≤ normalizer (V : Set G)) :
    Subgroup (internalActionImage M V hn) :=
  (D.subgroupOf M).map (actionHom M V hn).rangeRestrict

theorem actor_nontrivial {M V D : Subgroup G} (hn : M ≤ normalizer (V : Set G))
    (hDM : D ≤ M) (hmove : ¬ D ≤ centralizer (V : Set G)) :
    actor M V D hn ≠ ⊥ := by
  intro he
  change (D.subgroupOf M).map (actionHom M V hn).rangeRestrict = ⊥ at he
  have hh := (Subgroup.map_eq_bot_iff _).mp he
  rw [MonoidHom.ker_rangeRestrict, actionHom_ker] at hh
  exact hmove (fun x hx => hh (show (⟨x,hDM hx⟩ : M) ∈ D.subgroupOf M from hx))

theorem actor_elementary {M V D : Subgroup G} (hn : M ≤ normalizer (V : Set G))
    (hDM : D ≤ M) [IsElementaryAbelian 2 D] : IsElementaryAbelian 2 (actor M V D hn) := by
  let : IsElementaryAbelian 2 (D.subgroupOf M) := IsElementaryAbelian.subgroupOf hDM
  unfold actor
  exact IsElementaryAbelian.map _

theorem actor_quadratic {M V U A D : Subgroup G}
    [IsElementaryAbelian 2 V] (hn : M ≤ normalizer (V : Set G))
    (hVU : V ≤ U) (hDA : D ≤ A) (hquad : ⁅⁅U,A⁆,A⁆ = ⊥) :
    IsQuadratic (imageRepresentation M V hn) (actor M V D hn) := by
  have hc : A ≤ centralizer (⁅U,A⁆ : Subgroup G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hquad)
  rintro a ⟨a,ha,rfl⟩ b ⟨b,hb,rfl⟩ v
  apply Additive.toMul.injective
  apply Subtype.ext
  change (a : G) * ((b : G) * (v.toMul : G) * (b : G)⁻¹ / (v.toMul : G)) *
    (a : G)⁻¹ = (b : G) * (v.toMul : G) * (b : G)⁻¹ / (v.toMul : G)
  simp only [div_eq_mul_inv]
  have hm : ⁅(b : G),(v.toMul : G)⁆ ∈ ⁅U,A⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator (hDA hb) (hVU v.toMul.property)
  change (a : G) * ⁅(b : G),(v.toMul : G)⁆ * (a : G)⁻¹ = ⁅(b : G),(v.toMul : G)⁆
  have hcomm : (a : G) * ⁅(b : G),(v.toMul : G)⁆ =
      ⁅(b : G),(v.toMul : G)⁆ * (a : G) := (hc (hDA ha) _ hm).symm
  rw [hcomm,mul_inv_cancel_right]

private noncomputable def originalSection (M V : Subgroup G)
    [IsElementaryAbelian 2 V] (hn : M ≤ normalizer (V : Set G)) (hVM : V ≤ M) :
    BinaryConjugationSection M V ⊥ ((imageRepresentation M V hn).comp
      (actionHom M V hn).rangeRestrict) where
  section_le := hVM
  kernel_le := bot_le
  normalized := hn
  coordinates := {
    toFun v := Multiplicative.ofAdd (Additive.ofMul v)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  onto := fun v => ⟨v.toAdd.toMul,rfl⟩
  kernel_eq := by ext x; exact Subtype.val_inj.symm
  equivariant := fun _ _ => rfl

set_option backward.isDefEq.respectTransparency false in
theorem commutator_card_image {M V D : Subgroup G} [Finite G]
    [IsElementaryAbelian 2 V] (hn : M ≤ normalizer (V : Set G))
    (hVM : V ≤ M) (hDM : D ≤ M) :
    Nat.card (⁅V,D⁆ : Subgroup G) = 2 ^ Module.finrank (ZMod 2)
      (subspaceCommutator (imageRepresentation M V hn) ⊤
        ((D.subgroupOf M).map (actionHom M V hn).rangeRestrict)) := by
  let c := originalSection M V hn hVM
  have hDV : ⁅V,D⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp (hDM.trans hn)
  let e : (⁅V,D⁆ : Subgroup G) ≃ c.imageSpace ⁅V,D⁆ := {
    toFun x := ⟨Additive.ofMul ⟨x,hDV x.property⟩,
      (c.mem_imageSpace_iff _ _).mpr ⟨⟨x,hDV x.property⟩,x.property,rfl⟩⟩
    invFun v := ⟨v.val.toMul, by
      obtain ⟨x,hx,he⟩ := (c.mem_imageSpace_iff _ _).mp v.property
      change Additive.ofMul x = v.val at he
      exact congrArg (fun a : Additive V => (a.toMul : G)) he ▸ hx⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have ht : c.imageSpace V = ⊤ := by
    apply top_unique
    intro v _
    exact (c.mem_imageSpace_iff _ _).mpr ⟨v.toMul,v.toMul.property,rfl⟩
  have he := c.imageSpace_commutator D V hDM le_rfl
  rw [commutator_comm,ht,subspaceCommutator_comp_map] at he
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,he]

theorem normalized_commutator_of_abelian_image {M V T D : Subgroup G}
    (hn : M ≤ normalizer (V : Set G)) (hVM : V ≤ M) (hTM : T ≤ M) (hDT : D ≤ T)
    (hab : IsMulCommutative ((T.subgroupOf M).map (actionHom M V hn).rangeRestrict)) :
    T ≤ normalizer (⁅V,D⁆ : Subgroup G) := by
  let W := V.subgroupOf M
  let S := T.subgroupOf M
  let B := D.subgroupOf M
  let : W.Normal := normal_subgroupOf_of_le_normalizer hn
  let f := (actionHom M V hn).rangeRestrict
  let q := QuotientGroup.mk' (centralizer (W : Set M))
  have hk : f.ker = centralizer (W : Set M) := by
    rw [MonoidHom.ker_rangeRestrict,actionHom_ker]
    ext g
    constructor
    · intro hg v hv
      exact Subtype.ext (hg v hv)
    · intro hg v hv
      exact congrArg Subtype.val (hg ⟨v,hVM hv⟩ hv)
  have hc : ⁅S,S⁆ ≤ centralizer (W : Set M) := by
    rw [←hk,←Subgroup.map_eq_bot_iff,map_commutator]
    exact commutator_self_eq_bot_iff.mpr hab
  have hB : B ≤ S := fun _ hx => hDT hx
  have hq : ⁅S.map q,B.map q⁆ = ⊥ := by
    rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    exact (commutator_mono le_rfl hB).trans hc
  have hs : S ≤ normalizer (⁅W,B⁆ : Subgroup M) :=
    (map_le_iff_le_comap.mp ((commutator_eq_bot_iff_le_centralizer.mp hq).trans
      (Subgroup.centralizer_le_normalizer _))).trans (normalizer_centralizerQuotient_image_le W B)
  have hm := (map_mono (f := M.subtype) hs).trans (le_normalizer_map M.subtype)
  simpa only [S,W,B,map_commutator,map_subgroupOf_eq_of_le hVM,
    map_subgroupOf_eq_of_le hTM,map_subgroupOf_eq_of_le (hDT.trans hTM)] using hm

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
