module
public import CFSG.Quasithin.Chapter3.Section01.SourceNumericalOutsideReduction
public import CFSG.Quasithin.Chapter3.Section01.SourceE213ActionTransfer
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddDegreeThree.WeakSource
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.WeakSource
/-!
# The remaining small source models for the outside-core bound

The no-TI large-prime PSL3 calculation removes every odd linear row except
PSL3(3). The order-two and full-plane pair constructions remove both endpoints
of the symplectic image range. The original qrc action therefore has cubic
ratio at most two unless its literal quotient image is noncyclic and lies
in one of the two displayed cases. No extra source hypothesis is introduced.

Source: Aschbacher--Smith E.2.7--13, printed pp.219--225, and the original
3.1.6 outside-core application, printed pp.573--574. The remaining PSL3(3)
geometry and proper symplectic-pair recognition are not asserted here.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- The two exact remaining models and the size of the original module image. -/
@[expose] def QrcHypotheses.HasSmallExceptionalOutsideCoreModel
    (h : QrcHypotheses T M M₀ H V) : Prop :=
  ∃ hp : ChapterB.IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤,
  ∃ K : Subgroup H, K.IsCComponent ∧ K.Normal ∧
    K ⊔ ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H) = ⊤ ∧
    let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore (T.subtype h.right_mem.1.1.2) hp)
    2 < Nat.card ((V.subgroupOf H).map q) ∧
      (ClassicalGroup.IsPSL (K.map q) 3 3 ∨
       ∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp (K.map q) 2 (2^f) ∧
         Nat.card ((V.subgroupOf H).map q) < (2^f)^2)

/-- The original outside-core numerical bound, except for the two precise small-image cases. -/
theorem QrcHypotheses.outsideCore_cubicRatio_le_two_or_small_exceptional_model
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hout : ¬ V ≤ H.pCoreIn 2) :
    letI := h.module_elementary
    cubicRatio (imageRepresentation M₀ V h.module_normalized) ≤ 2 ∨
      h.HasSmallExceptionalOutsideCoreModel := by
  let := h.module_elementary
  rcases h.outsideCore_cubicRatio_le_two_or_exceptional_model hG hM hu hout with hb | hm
  · exact Or.inl hb
  obtain ⟨hp,K,hK,hN,hgen,hm⟩ := hm
  let S := T.subtype h.right_mem.1.1.2
  let W := V.subgroupOf H
  have hVH : V ≤ H := h.module_le_sylow.trans h.right_mem.1.1.2
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVH
  have hWS : W ≤ (S : Subgroup H) := fun _ hx => h.module_le_sylow hx
  have hTV : (S : Subgroup H) ≤ normalizer (W : Set H) := h.intrinsic_module_normalized
  have hvn : (W.subgroupOf (S : Subgroup H)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hWS).mpr hTV
  have hWcore : W ≤ (ChapterB.minimalParabolicMax S hp).pCoreIn 2 :=
    h.intrinsic_module_le_maximal_core hG hM hp
  have hWout : ¬ W ≤ ChapterB.minimalParabolicCore S hp := by
    intro he
    have hc : W ≤ pCore 2 H := by
      rw [←ChapterB.minimalParabolic_sylow_inf_core S hp]
      exact le_inf hWS he
    apply hout
    have hmap := map_mono (f := H.subtype) hc
    change (V.subgroupOf H).map H.subtype ≤ H.pCoreIn 2 at hmap
    simpa only [map_subgroupOf_eq_of_le hVH] using hmap
  have hfit : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp
        (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) h.right_mem.1.1))
  let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore S hp)
  by_cases hsmall : Nat.card (W.map q) = 2
  · exact Or.inl (h.cubicRatio_le_nat_of_intrinsic_action 2
      (ChapterE.Witnesses.SymplecticFour.source_order_two_cubicRatio_le_two
        S hp W S hWS hvn hWcore hsmall hfit le_rfl hTV))
  have hne : W.map q ≠ ⊥ := by
    intro he
    exact hWout (by simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff W).mp he)
  have htwo : 2 < Nat.card (W.map q) := by
    have hc := (one_lt_card_iff_ne_bot _).mpr hne
    omega
  let := hN
  have hs : ¬ Group.IsSolvable H := by
    intro hsol
    let := hsol
    exact hK.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective (f := K.subtype) K.subtype_injective)
  rcases hm with ⟨p,hpprime,hpodd,hm⟩ | ⟨n,hn,hm⟩
  · by_cases h3 : p = 3
    · subst p
      exact Or.inr ⟨hp,K,hK,hN,hgen,htwo,Or.inl hm⟩
    have hp3 : 3 < p := by
      have := hpprime.two_le
      have : p ≠ 2 := by intro he; subst p; norm_num at hpodd
      omega
    exact Or.inl (h.cubicRatio_le_nat_of_intrinsic_action 2
      (ChapterE.Witnesses.OddDegreeThree.source_cubicRatio_le_two_of_three_lt
        S hp hs K hK hgen hpprime hpodd hp3 hm W S hWS hvn hWcore hWout hfit le_rfl hTV))
  · rcases ChapterE.Witnesses.SymplecticFour.source_cubicRatio_le_two_or_middle_image
      S hp hs K hK hgen (by omega) hm W S hWS hvn hWcore hWout hfit le_rfl hTV with hb | hmid
    · exact Or.inl (h.cubicRatio_le_nat_of_intrinsic_action 2 hb)
    · exact Or.inr ⟨hp,K,hK,hN,hgen,htwo,Or.inr ⟨n,hn,hm,hmid.2⟩⟩
end CFSG.Quasithin.Chapter3
