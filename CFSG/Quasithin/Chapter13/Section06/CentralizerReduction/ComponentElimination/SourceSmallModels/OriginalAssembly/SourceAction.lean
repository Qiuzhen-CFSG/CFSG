module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SourcePreparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.JoinKernel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.AlternatingModels
/-!
# The original join action and its full moved subgroup

The original plus map restricts to the literal component--Sylow join. Its
normal elementary seed module is linearly identified with W_K, retaining
conjugation, its kernel, and the original Thompson movement. The B.5 moved
section identifies the actual U_K=[W_K,K]. Faithfulness gives its exact
centralizer kernel, the zero central layer gives zero component fixed points,
and two-perfection gives [U_K,K]=U_K.

The natural model's embedding and fixed codimensions transport along this
same quotient map. These are the literal group-action inputs to the natural
and exceptional C.1.24 seed theorems, with no shortness premise.
Source: Aschbacher--Smith C.1.24 and 13.6.22, printed pp.130--131 and 932.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
open ChapterB.QuasisimpleSource ComponentSelection SourceContainment SourceContainment.LinearThree.CentralAction.ModuleAlternatives
variable {G : Type*} [Group G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))

theorem plusActor_eq_join (hn : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K) :
    plusActor K L T v = K ⊔ Tv T v := by
  rw [plusActor,Kminus_eq_of_invariant K T v hn,sup_eq_left.mpr hLK]

theorem joinPlusMap_surjective (hn : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K) :
    Function.Surjective (joinPlusMap K L T z v hL hz) := by
  intro a
  obtain ⟨x,hx⟩ := plusMk_surjective K L T z v hL hz a
  exact ⟨⟨x, (plusActor_eq_join K L T v hn hLK) ▸ x.property⟩, hx⟩

theorem joinPlusMap_image (X : Subgroup G) (hX : X ≤ K ⊔ Tv T v) :
    (X.subgroupOf (K ⊔ Tv T v)).map (joinPlusMap K L T z v hL hz) =
      plusImage K L T z v hL hz X := by
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨inclusion (sup_le (K_le_plusActor K L T v) le_sup_right) x,hx,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hX hx⟩,hx,rfl⟩

theorem WK_le_join (hn : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hzT : z ∈ Tv T v) : WK K L T z v ≤ K ⊔ Tv T v := by
  rw [WK,Kminus_eq_of_invariant K T v hn]
  apply conjugateSpanBy_le (zpowers_le.mpr
    ((show Tv T v ≤ K ⊔ Tv T v from le_sup_right) hzT))
  exact (sup_le le_sup_left (hLK.trans le_sup_left)).trans (K ⊔ Tv T v).le_normalizer

include hL hz in
theorem joinWK_normal : ((WK K L T z v).subgroupOf (K ⊔ Tv T v)).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((sup_le (K_le_plusActor K L T v) le_sup_right).trans
      (plusActor_normalizes_WK K L T z v hL hz))

theorem joinPlusMap_ker (hW : WK K L T z v ≤ K ⊔ Tv T v) :
    (joinPlusMap K L T z v hL hz).ker =
      centralizer ((WK K L T z v).subgroupOf (K ⊔ Tv T v) : Set (K ⊔ Tv T v : Subgroup G)) := by
  ext a
  change plusMk K L T z v hL hz
    (inclusion (sup_le (K_le_plusActor K L T v) le_sup_right) a) = 1 ↔ _
  change inclusion (sup_le (K_le_plusActor K L T v) le_sup_right) a ∈
    (plusMk K L T z v hL hz).ker ↔ _
  rw [plusMk_ker]
  constructor
  · intro ha w hw
    exact Subtype.ext (ha w hw)
  · intro ha w hw
    exact congrArg Subtype.val (ha ⟨w,hW hw⟩ hw)

theorem join_thompson_movement (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ Tv T v : Subgroup G))
    (hP : (P : Subgroup (K ⊔ Tv T v : Subgroup G)).map (K ⊔ Tv T v).subtype = Tv T v) :
    ¬ elementaryAbelianMaxJ (P : Subgroup (K ⊔ Tv T v : Subgroup G)) ≤
      (joinPlusMap K L T z v hL hz).ker := by
  intro hzero
  have hJ : (elementaryAbelianMaxJ (Tv T v)).subgroupOf (K ⊔ Tv T v) =
      elementaryAbelianMaxJ (P : Subgroup (K ⊔ Tv T v : Subgroup G)) := by
    have he : (elementaryAbelianMaxJ (P : Subgroup (K ⊔ Tv T v : Subgroup G))).map
        (K ⊔ Tv T v).subtype = elementaryAbelianMaxJ (Tv T v) := by
      rw [←elementaryAbelianMaxJ_map_injective _ (K ⊔ Tv T v).subtype_injective,hP]
    rw [←he]
    exact comap_map_eq_self_of_injective (K ⊔ Tv T v).subtype_injective _
  have hm : plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v)) = ⊥ := by
    rw [←joinPlusMap_image K L T z v hL hz _
      ((show elementaryAbelianMaxJ (Tv T v) ≤ Tv T v from sSup_le fun _ h => h.1).trans le_sup_right), hJ]
    exact (Subgroup.map_eq_bot_iff _).mpr hzero
  have hc := component_plus_commutator K L T z v hL hz hK hn
  rw [hm,commutator_bot_right] at hc
  exact plusImage_ne_bot_of_mem_Yz K L T z v hL hz hK hc.symm

variable [IsElementaryAbelian 2 (WK K L T z v)]

noncomputable def joinWKEquiv (hW : WK K L T z v ≤ K ⊔ Tv T v)
    [IsElementaryAbelian 2 ((WK K L T z v).subgroupOf (K ⊔ Tv T v))] :
    Additive ((WK K L T z v).subgroupOf (K ⊔ Tv T v)) ≃ₗ[ZMod 2]
      Additive (WK K L T z v) :=
  { (subgroupOfEquivOfLe hW).toAdditive with
    map_smul' := ZMod.map_smul (subgroupOfEquivOfLe hW).toMonoidHom.toAdditive }

theorem joinWKEquiv_intertwines (hW : WK K L T z v ≤ K ⊔ Tv T v)
    [_hN : ((WK K L T z v).subgroupOf (K ⊔ Tv T v)).Normal]
    [IsElementaryAbelian 2 ((WK K L T z v).subgroupOf (K ⊔ Tv T v))]
    (hq : Function.Surjective (joinPlusMap K L T z v hL hz))
    (a : Gplus K L T z v hL hz)
    (w : Additive ((WK K L T z v).subgroupOf (K ⊔ Tv T v))) :
    joinWKEquiv K L T z v hW
      (NormalElementaryQuotient.representation _ _ hq
        (joinPlusMap_ker K L T z v hL hz hW) a w) =
      wkRepresentation K L T z v hL hz a (joinWKEquiv K L T z v hW w) := by
  obtain ⟨a,rfl⟩ := hq a
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (congrArg Subtype.val (NormalElementaryQuotient.representation_apply _ _ hq
    (joinPlusMap_ker K L T z v hL hz hW) a w)).trans
      (wkRepresentation_apply K L T z v hL hz
        (inclusion (sup_le (K_le_plusActor K L T v) le_sup_right) a)
        (joinWKEquiv K L T z v hW w)).symm


include hL hz in
omit [IsElementaryAbelian 2 (WK K L T z v)] in
theorem join_normalizes_UK (hn : Tv T v ≤ normalizer (K : Set G)) :
    K ⊔ Tv T v ≤ normalizer (UK K L T z v : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq,UK,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp
      (plusActor_normalizes_WK K L T z v hL hz
        ((sup_le (K_le_plusActor K L T v) le_sup_right) hg)),
    mem_normalizer_iff_map_conj_eq.mp ((sup_le K.le_normalizer hn) hg)]

include hL hz in
omit [IsElementaryAbelian 2 (WK K L T z v)] in
theorem joinUK_normal (hn : Tv T v ≤ normalizer (K : Set G)) :
    ((UK K L T z v).subgroupOf (K ⊔ Tv T v)).Normal :=
  normal_subgroupOf_of_le_normalizer (join_normalizes_UK K L T z v hL hz hn)

noncomputable def joinUKMulEquiv (hW : WK K L T z v ≤ K ⊔ Tv T v)
    (s : MovedSection (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K)) :
    ((UK K L T z v).subgroupOf (K ⊔ Tv T v)) ≃* Multiplicative s.space.toSubmodule :=
  (subgroupOfEquivOfLe ((UK_le_WK K L T z v hL hz).trans hW)).trans
    (movedEquivUK K L T z v hL hz s).symm

theorem joinUK_card (hW : WK K L T z v ≤ K ⊔ Tv T v)
    (s : MovedSection (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K)) :
    Nat.card ((UK K L T z v).subgroupOf (K ⊔ Tv T v)) = Nat.card s.space.toSubmodule :=
  (Nat.card_congr (joinUKMulEquiv K L T z v hL hz hW s).toEquiv).trans
    (Nat.card_congr Multiplicative.toAdd)

theorem joinPlusMap_ker_UK (hW : WK K L T z v ≤ K ⊔ Tv T v)
    (s : MovedSection (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K)) (hs : Function.Injective s.space.toRepresentation) :
    (joinPlusMap K L T z v hL hz).ker =
      centralizer ((UK K L T z v).subgroupOf (K ⊔ Tv T v) : Set (K ⊔ Tv T v : Subgroup G)) := by
  apply le_antisymm
  · rw [joinPlusMap_ker K L T z v hL hz hW]
    exact centralizer_le (comap_mono (UK_le_WK K L T z v hL hz))
  · intro a ha
    apply hs
    rw [map_one]
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((wkRepresentation K L T z v hL hz
      (plusMk K L T z v hL hz
        (inclusion (sup_le (K_le_plusActor K L T v) le_sup_right) a)) w.val).toMul : G) = _
    rw [wkRepresentation_apply]
    have hu : (w.val.toMul : G) ∈ UK K L T z v :=
      (moved_eq_ukSubspace K L T z v hL hz).le (s.space_eq.le w.property)
    have hc := congrArg Subtype.val
      (ha ⟨w.val.toMul, hW ((UK_le_WK K L T z v hL hz) hu)⟩ hu)
    change (w.val.toMul : G) * (a : G) = (a : G) * (w.val.toMul : G) at hc
    change (a : G) * (w.val.toMul : G) * (a : G)⁻¹ = (w.val.toMul : G)
    rw [←hc,mul_inv_cancel_right]

theorem joinUK_fixed_eq_bot (hK : K ≤ Gv v)
    (hW : WK K L T z v ≤ K ⊔ Tv T v)
    (s : MovedSection (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K)) (hs : s.central.toSubmodule = ⊥) :
    (UK K L T z v).subgroupOf (K ⊔ Tv T v) ⊓
      centralizer (K.subgroupOf (K ⊔ Tv T v) : Set (K ⊔ Tv T v : Subgroup G)) = ⊥ := by
  apply bot_unique
  intro u hu
  let w := ((joinUKMulEquiv K L T z v hL hz hW s) ⟨u,hu.1⟩).toAdd
  have hc : (w.val.toMul : G) ∈ centralizer (K : Set G) := by
    intro k hk
    exact congrArg Subtype.val (hu.2 ⟨k,(show K ≤ K ⊔ Tv T v from le_sup_left) hk⟩ hk)
  have hw := (mem_sectionCentral_iff K L T z v hL hz hK s w).mpr hc
  rw [hs] at hw
  change w = 0 at hw
  exact Subtype.ext (congrArg (fun w : s.space.toSubmodule => (w.val.toMul : G)) hw)


include hL hz in
theorem joinUK_commutator_self [Finite G] (hpK : IsPPerfect 2 K)
    (hW : WK K L T z v ≤ K ⊔ Tv T v) :
    ⁅(UK K L T z v).subgroupOf (K ⊔ Tv T v), K.subgroupOf (K ⊔ Tv T v)⁆ =
      (UK K L T z v).subgroupOf (K ⊔ Tv T v) := by
  apply map_injective (K ⊔ Tv T v).subtype_injective
  rw [map_commutator,map_subgroupOf_eq_of_le ((UK_le_WK K L T z v hL hz).trans hW),
    map_subgroupOf_eq_of_le (show K ≤ K ⊔ Tv T v from le_sup_left)]
  exact commutator_isPPerfect_idempotent K (WK K L T z v) hpK
    (IsElementaryAbelian.isPGroup 2 _) ((K_le_plusActor K L T v).trans
      (plusActor_normalizes_WK K L T z v hL hz))


private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hn hp
  let := hn
  let : Group.IsNilpotent (A ⧸ N) := hp.isNilpotent
  apply top_unique
  rw [←solvableResidual_eq_top (G := A)]
  exact solvableResidual_le_of_solvable_quotient N

variable [Finite G]

/-- The original B.5 classification supplies the full moved subgroup
and every literal group-action input used after seed propagation. -/
theorem join_moved_inputs
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hLK : Lv L v ≤ K) (hzT : z ∈ Tv T v)
    (m : AlternatingModels.ActionData (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K)) :
    let H := K ⊔ Tv T v
    let B := K.subgroupOf H
    let U := (UK K L T z v).subgroupOf H
    U.Normal ∧ IsElementaryAbelian 2 U ∧ ⁅U,B⁆ = U ∧
      U ⊓ centralizer (B : Set H) = ⊥ ∧
      (joinPlusMap K L T z v hL hz).ker = centralizer (U : Set H) ∧
      (Nat.card U = 2 ^ 6 ∨ Nat.card U = 2 ^ 4) := by
  let H := K ⊔ Tv T v
  have hW := WK_le_join K L T z v hn hLK hzT
  have hU := (UK_le_WK K L T z v hL hz).trans hW
  let : IsElementaryAbelian 2 (UK K L T z v) :=
    IsElementaryAbelian.of_le (UK_le_WK K L T z v hL hz)
  let : Group.IsPerfect (K.subgroupOf H) := hK.1.2.1.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)).surjective
  let s : MovedSection (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K) :=
    ⟨m.sectionData.space,m.sectionData.space_eq,m.sectionData.central,m.sectionData.central_eq⟩
  refine ⟨joinUK_normal K L T z v hL hz hn,IsElementaryAbelian.subgroupOf hU,
    joinUK_commutator_self K L T z v hL hz perfect_twoPerfect hW,
    joinUK_fixed_eq_bot K L T z v hL hz hK.1.1 hW s m.central_eq_bot,
    joinPlusMap_ker_UK K L T z v hL hz hW s m.faithful,?_⟩
  rw [joinUK_card K L T z v hL hz hW s]
  rcases m.models with ⟨e,_⟩ | ⟨_,hd⟩
  · left
    rw [Nat.card_congr e.linearEquiv.toEquiv,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      BinaryPermutation.finrank_natural_odd (Fin 7) (by decide), Fintype.card_fin]
  · right
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,hd]


omit [IsElementaryAbelian 2 (WK K L T z v)] [Finite G] in
theorem join_core_quasisimple
    (h : IsQuasisimple (K ⧸ pCore 2 K)) :
    IsQuasisimple ((K.subgroupOf (K ⊔ Tv T v)) ⧸ pCore 2 (K.subgroupOf (K ⊔ Tv T v))) := by
  let e := subgroupOfEquivOfLe (show K ≤ K ⊔ Tv T v from le_sup_left)
  let eQ := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let := h
  exact IsQuasisimple.of_mulEquiv eQ.symm

omit [IsElementaryAbelian 2 (WK K L T z v)] [Finite G] in
theorem join_component_normal (hn : Tv T v ≤ normalizer (K : Set G)) :
    (K.subgroupOf (K ⊔ Tv T v)).Normal :=
  normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)


omit [Finite G] in
theorem joinWKEquiv_relabel_intertwines {Q : Type*} [Group Q]
    (hW : WK K L T z v ≤ K ⊔ Tv T v)
    [_hN : ((WK K L T z v).subgroupOf (K ⊔ Tv T v)).Normal]
    [IsElementaryAbelian 2 ((WK K L T z v).subgroupOf (K ⊔ Tv T v))]
    (e : Gplus K L T z v hL hz ≃* Q)
    (hq : Function.Surjective (e.toMonoidHom.comp (joinPlusMap K L T z v hL hz)))
    (hk : (e.toMonoidHom.comp (joinPlusMap K L T z v hL hz)).ker =
      centralizer ((WK K L T z v).subgroupOf (K ⊔ Tv T v) : Set (K ⊔ Tv T v : Subgroup G)))
    (a : Q) (w : Additive ((WK K L T z v).subgroupOf (K ⊔ Tv T v))) :
    joinWKEquiv K L T z v hW (NormalElementaryQuotient.representation _ _ hq hk a w) =
      wkRepresentation K L T z v hL hz (e.symm a) (joinWKEquiv K L T z v hW w) := by
  obtain ⟨a,rfl⟩ := hq a
  change joinWKEquiv K L T z v hW (NormalElementaryQuotient.representation _ _ hq hk
    ((e.toMonoidHom.comp (joinPlusMap K L T z v hL hz)) a) w) =
      wkRepresentation K L T z v hL hz (e.symm (e (joinPlusMap K L T z v hL hz a))) _
  rw [e.symm_apply_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (congrArg Subtype.val (NormalElementaryQuotient.representation_apply _ _ hq hk a w)).trans
    (wkRepresentation_apply K L T z v hL hz
      (inclusion (sup_le (K_le_plusActor K L T v) le_sup_right) a)
      (joinWKEquiv K L T z v hW w)).symm

theorem join_natural_inputs
    (hW : WK K L T z v ≤ K ⊔ Tv T v)
    [_hN : ((WK K L T z v).subgroupOf (K ⊔ Tv T v)).Normal]
    [IsElementaryAbelian 2 ((WK K L T z v).subgroupOf (K ⊔ Tv T v))]
    (m : AlternatingModels.ActionData (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K))
    (e : CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ActionEquiv
      m.sectionData.space.toRepresentation (BinaryPermutation.naturalRepresentation (Fin 7)))
    (hq : Function.Surjective (e.groupEquiv.toMonoidHom.comp (joinPlusMap K L T z v hL hz)))
    (hk : (e.groupEquiv.toMonoidHom.comp (joinPlusMap K L T z v hL hz)).ker =
      centralizer ((WK K L T z v).subgroupOf (K ⊔ Tv T v) : Set (K ⊔ Tv T v : Subgroup G))) :
    let ρ := NormalElementaryQuotient.representation _ _ hq hk
    (∀ A, fixedCodim ρ A = fixedCodim (BinaryPermutation.naturalRepresentation (Fin 7)) A) ∧
    ∃ f : BinaryPermutation.natural (Fin 7) →ₗ[ZMod 2]
        Additive ((WK K L T z v).subgroupOf (K ⊔ Tv T v)),
      Function.Injective f ∧ ∀ a w,
        f (BinaryPermutation.naturalRepresentation (Fin 7) a w) = ρ a (f w) := by
  let τ := NormalElementaryQuotient.representation _ _ hq hk
  let ρ := wkRepresentation K L T z v hL hz
  let C := plusImage K L T z v hL hz K
  let E := joinWKEquiv K L T z v hW
  have he (a w) := joinWKEquiv_relabel_intertwines K L T z v hL hz hW e.groupEquiv hq hk a w
  constructor
  · intro A
    rw [fixedCodim_map_equivariant τ ρ e.groupEquiv.symm.toMonoidHom E he A,
      m.fixedCodim_natural ρ C e]
    congr 1
    rw [map_map]
    have hi : e.groupEquiv.toMonoidHom.comp e.groupEquiv.symm.toMonoidHom =
        MonoidHom.id _ := by apply MonoidHom.ext; intro x; exact e.groupEquiv.apply_symm_apply x
    rw [hi,Subgroup.map_id]
  · let f := E.symm.toLinearMap.comp (m.naturalLift ρ C e)
    refine ⟨f,E.symm.injective.comp (m.naturalLift_injective ρ C e),?_⟩
    intro a w
    apply E.injective
    change E (E.symm (m.naturalLift ρ C e
      (BinaryPermutation.naturalRepresentation (Fin 7) a w))) = E (τ a (f w))
    rw [E.apply_symm_apply,he]
    change m.naturalLift ρ C e (BinaryPermutation.naturalRepresentation (Fin 7) a w) =
      ρ (e.groupEquiv.symm a) (E (E.symm (m.naturalLift ρ C e w)))
    rw [E.apply_symm_apply]
    have hh := m.naturalLift_intertwines ρ C e (e.groupEquiv.symm a) w
    simpa only [e.groupEquiv.apply_symm_apply] using hh

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
