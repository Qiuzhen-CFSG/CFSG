module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.PreferredCanonicalSeven
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.AlternatingSevenMoved
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# The full canonical A7 moved module

The literal subgroup V_v of order32 lies in [U,K_v]. On the actual canonical
quotient action, B.5.1 and the A7 component marking therefore exclude the
exceptional four-space. The full moved space is the natural six-space and
complements the original component fixed space. Injective transport gives
|[U,K_v]|=64, C_[U,K_v](K_v)=1 and U=[U,K_v] C_U(K_v) in the original G.

PreferredCanonicalModule supplies the actual same-point application. The FF
witness remains explicit and is still an obligation of this source owner;
no source assertion12.6.2 or12.6.23 follows here. Earlier invariance/TI retain
qt-d-1222-source; final discharge remains with qt-d-12634-source.
Source: Aschbacher--Smith12.6.18, printed p.827, using B.5.1 and I.1.6,
combined manuscript of 1 March 2004.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open ChapterB.QuasisimpleSource

/-- The entire canonical moved space, with its actual component image,
quotient action, natural coordinates and complementary fixed space. -/
@[expose] def CanonicalSevenMoved {A : Type*} [Group A]
    (E : Subgroup A) [E.Normal] [IsElementaryAbelian 2 E] (K : Subgroup A) : Prop :=
  let ρ := ChapterB.InternalThompsonAction.action E
  let B := K.map (ChapterB.InternalThompsonAction.actionMk E)
  let O := offenderSubgroup ρ
  B ≤ O ∧ ∃ s : MovedSection (ρ.comp O.subtype) (B.subgroupOf O),
    IsCompl s.space.toSubmodule (fixedSpace (ρ.comp O.subtype) (B.subgroupOf O)) ∧
      IsAlternatingNatural (s.space.toRepresentation.comp (B.subgroupOf O).subtype) 7

/-- The marked natural action gives the order, zero moved fixed space, and
direct decomposition on the literal internal subgroups. -/
theorem canonical_seven_moved_properties {A : Type*} [Group A] [Finite A]
    (E : Subgroup A) [E.Normal] [IsElementaryAbelian 2 E] (K : Subgroup A)
    (h : CanonicalSevenMoved E K) :
    Nat.card (⁅E,K⁆ : Subgroup A) = 64 ∧
      (⁅E,K⁆ : Subgroup A) ⊓ centralizer (K : Set A) = ⊥ ∧
      E = ⁅E,K⁆ ⊔ (E ⊓ centralizer (K : Set A)) := by
  let q := ChapterB.InternalThompsonAction.actionMk E
  let ρ := ChapterB.InternalThompsonAction.action E
  let B := K.map q
  let O := offenderSubgroup ρ
  let C := B.subgroupOf O
  obtain ⟨hBO,s,hs,⟨a⟩⟩ := h
  have hspace : s.space.toSubmodule = subspaceCommutator ρ ⊤ B := by
    rw [s.space_eq]
    change subspaceCommutator (ρ.comp O.subtype) ⊤ C = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hBO]
  have hmem (u : Additive E) : u ∈ s.space.toSubmodule ↔ (u.toMul : A) ∈ ⁅E,K⁆ := by
    rw [hspace]
    change u ∈ subspaceCommutator (NormalElementaryQuotient.representation E q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ⊤ (K.map q) ↔ _
    rw [←NormalElementaryQuotient.commutatorSpace_eq E q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) K]
    rfl
  have hfix (u : Additive E) :
      u ∈ fixedSpace (ρ.comp O.subtype) C ↔ (u.toMul : A) ∈ centralizer (K : Set A) := by
    constructor
    · intro hu
      apply mem_centralizer_iff.mpr
      intro k hk
      have hx : q k ∈ B := mem_map_of_mem q hk
      have hh := hu (⟨⟨q k,hBO hx⟩,hx⟩ : C)
      have he := congrArg (fun z : Additive E => (z.toMul : A)) hh
      change ((ChapterB.InternalThompsonAction.action E (q k) u).toMul : A) = _ at he
      rw [ChapterB.InternalThompsonAction.action_apply] at he
      exact mul_inv_eq_iff_eq_mul.mp he
    · intro hu c
      obtain ⟨k,hk,hkc⟩ := c.property
      change q k = c.val.val at hkc
      change ρ c.val.val u = u
      rw [←hkc]
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [ChapterB.InternalThompsonAction.action_apply]
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hu k hk)
  let W := (⁅E,K⁆ : Subgroup A)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left E K)
  let e := (NormalElementaryQuotient.movedEquiv E q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) K).trans
      (LinearEquiv.ofEq _ _ hspace.symm)
  have hc : Nat.card W = 64 := by
    rw [Nat.card_congr (Additive.ofMul : W ≃ Additive W),Nat.card_congr e.toEquiv,
      Nat.card_congr a.linearEquiv.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod,BinaryPermutation.finrank_natural_odd (Fin 7) (by decide)]
    rfl
  refine ⟨hc,?_,?_⟩
  · apply bot_unique
    intro x hx
    let u : Additive E := Additive.ofMul ⟨x,commutator_le_left E K hx.1⟩
    have hu : u ∈ (⊥ : Submodule (ZMod 2) (Additive E)) :=
      (disjoint_iff.mp hs.disjoint).le ⟨(hmem u).mpr hx.1,(hfix u).mpr hx.2⟩
    exact congrArg (fun z : Additive E => (z.toMul : A)) (show u = 0 from hu)
  · apply le_antisymm ?_ (sup_le (commutator_le_left E K) inf_le_left)
    intro x hx
    let u : Additive E := Additive.ofMul ⟨x,hx⟩
    have hu : u ∈ s.space.toSubmodule ⊔ fixedSpace (ρ.comp O.subtype) C := hs.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨y,hy,z,hz,he⟩ := Submodule.mem_sup.mp hu
    have hm : (y.toMul : A) * (z.toMul : A) ∈ ⁅E,K⁆ ⊔ (E ⊓ centralizer (K : Set A)) :=
      mul_mem (mem_sup_left ((hmem y).mp hy)) (mem_sup_right ⟨z.toMul.property,(hfix z).mp hz⟩)
    have hev := congrArg (fun z : Additive E => (z.toMul : A)) he
    change (y.toMul : A) * (z.toMul : A) = x at hev
    exact hev ▸ hm

/-- An injective ambient inclusion preserves all three original subgroup conclusions. -/
theorem canonical_seven_moved_properties_map {A G : Type*} [Group A] [Finite A] [Group G]
    (E : Subgroup A) [E.Normal] [IsElementaryAbelian 2 E] (K : Subgroup A)
    (h : CanonicalSevenMoved E K) (f : A →* G) (hf : Function.Injective f) :
    Nat.card ((⁅E,K⁆ : Subgroup A).map f) = 64 ∧
      (⁅E,K⁆ : Subgroup A).map f ⊓ centralizer (K.map f : Set G) = ⊥ ∧
      E.map f = (⁅E,K⁆ : Subgroup A).map f ⊔ (E.map f ⊓ centralizer (K.map f : Set G)) := by
  obtain ⟨hc,hfix,hsplit⟩ := canonical_seven_moved_properties E K h
  refine ⟨?_,?_,?_⟩
  · rwa [card_map_of_injective hf]
  · rw [map_inf_centralizer_of_injective f hf,hfix,Subgroup.map_bot]
  · have hh := congrArg (Subgroup.map f) hsplit
    rwa [Subgroup.map_sup,←map_inf_centralizer_of_injective f hf] at hh

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- In the canonical A7 case, the original V_v excludes the exceptional
four-space and identifies the full moved module, conditional only on FF. -/
theorem SourceHypothesis.nonsingular_canonical_seven_moved
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (S : Sylow 2 (Gv (v : G)))
    (hseven : Nonempty (Star (Kv (v : G)) ≃* alternatingGroup (Fin 7)))
    (hred : U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) =
      (reducedTwoSubgroup (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)).map
        (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G).subtype)
    (hm : Vv L V (v : G) ≤ ⁅U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype),Kv (v : G)⁆)
    (hker : centralizer (reducedTwoSubgroup (Kv (v : G) ⊔
      (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G) :
      Set (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)) =
        pCore 2 (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)) :
    let J := Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    let E := reducedTwoSubgroup J
    letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
    IsFFModule (ChapterB.InternalThompsonAction.action E) →
      CanonicalSevenMoved E ((Kv (v : G)).subgroupOf J) := by
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := Kv (v : G) ⊔ S₀
  let E := reducedTwoSubgroup J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  let K := (Kv (v : G)).subgroupOf J
  let q := ChapterB.InternalThompsonAction.actionMk E
  let ρ := ChapterB.InternalThompsonAction.action E
  let B := K.map q
  let O := offenderSubgroup ρ
  let C := B.subgroupOf O
  change IsFFModule ρ → CanonicalSevenMoved E K
  intro hff
  obtain ⟨_,_,hBO,⟨c⟩⟩ := H.nonsingular_canonical_quasisimple_of_ff D v hv
    S₀ (map_subtype_le _) (S.isPGroup'.map _) hker hff
  obtain ⟨b⟩ := H.nonsingular_canonical_component_image D v hv S₀ (map_subtype_le _) hker
  obtain ⟨e₇⟩ := hseven
  let e : C ≃* alternatingGroup (Fin 7) := (subgroupOfEquivOfLe hBO).trans (b.trans e₇)
  let s := c.sectionData
  have hspace : s.space.toSubmodule = subspaceCommutator ρ ⊤ B := by
    rw [s.space_eq]
    change subspaceCommutator (ρ.comp O.subtype) ⊤ C = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hBO]
  let W := (⁅E,K⁆ : Subgroup J)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left E K)
  let a := (NormalElementaryQuotient.movedEquiv E q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) K).trans
      (LinearEquiv.ofEq _ _ hspace.symm)
  have hcmap : W.map J.subtype = ⁅U (Kv (v : G)) S₀,Kv (v : G)⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le (show Kv (v : G) ≤ J from le_sup_left),←hred]
  have hc : Nat.card (⁅U (Kv (v : G)) S₀,Kv (v : G)⁆ : Subgroup G) = Nat.card s.space.toSubmodule := by
    rw [←hcmap,card_map_of_injective J.subtype_injective,
      Nat.card_congr (Additive.ofMul : W ≃ Additive W),Nat.card_congr a.toEquiv]
  have hcard := Subgroup.card_le_of_le hm
  rw [D.nonsingular_moved_card H.chosen v hv,hc] at hcard
  exact ⟨hBO,s,SourceCompletion.AlternatingSevenActor.natural_moved_of_card_gt_sixteen c e (by change 16 < Nat.card s.space.toSubmodule; omega)⟩
end CFSG.Quasithin.Chapter12.Section06
