module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.NaturalRankTwoTwisted
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Bender
public import CFSG.Quasithin.ChapterA.Section02.OddModelTwoRank
public import Theory.Representation.SL2.PerfectCoreQuotientDegree
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.Mathieu.M24.LargeElementaryPerfectNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowNormalElementary
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.NormalElementaryBound
public import Theory.SpecificGroups.Held.SylowOrderBound
public import Theory.SpecificGroups.Held.TwoLocalCandidates.OrderObstruction
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.TwoLocalOrder
public import Theory.SpecificGroups.Janko4.BinaryEightSection
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.JankoFour



/-!
# Containing models for an odd-degree natural block

A centerless full-core natural SL₂(2^n) block normalized by a full Sylow
has an elementary core of rank 2n and order divisible by 2^(3n). For odd
n > 1 these bounds, the actual two-local orders, and the binary quotient
obstructions exclude every non-rank-two entry of the complete Theorem C
catalogue. The rank-one entries use local-component non-enlargement.

The original common-overcomponent application is in `OriginalEmbedding`.
This sieve assumes neither A.3.12 nor a parabolic-residual identification.
Source: Aschbacher–Smith A.3.12, pp.47–48, and 10.2.3(4), p.747.
The concrete ATLAS carrier calculations retain their imported attribution.
-/

public section
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall.NaturalEmbedding
open ChapterC ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02.LocalModels
open ChapterC.Section05.NormalizerControl.EmbeddingSelection
variable {G : Type*} [Group G] [Finite G] {J : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem local_perfect {S : Subgroup G} (hl : J ∈ localCComponents S) :
    Group.IsPerfect J := by
  let := hl.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show J ≤ J ⊔ S from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective

omit [Finite G] in
private theorem core_card (h : IsL2EvenBlock J n) (hc : pCore 2 J = blockU J)
    (hz : center J = ⊥) : Nat.card (J.pCoreIn 2) = 2^(2*n) := by
  rw [pCoreIn,card_map_of_injective J.subtype_injective]
  exact NaturalRankTwo.core_card h hc hz

private theorem rank_bound (h : IsL2EvenBlock J n) (hc : pCore 2 J = blockU J)
    (hz : center J = ⊥) : 2*n ≤ primeRank 2 G := by
  let : IsElementaryAbelian 2 (pCore 2 J) := hc ▸ h.2.1.elementary
  let : IsElementaryAbelian 2 (J.pCoreIn 2) := IsElementaryAbelian.map J.subtype
  exact IsElementaryAbelian.primeRank_ge_of_card (J.pCoreIn 2) (core_card h hc hz)

private theorem order_dvd (h : IsL2EvenBlock J n) (hc : pCore 2 J = blockU J)
    (hz : center J = ⊥) : 2^(3*n)*((2^n)^2-1) ∣ Nat.card G := by
  rw [←NaturalBlock.card h hc hz]
  exact J.card_subgroup_dvd_card

private theorem two_power_dvd (h : IsL2EvenBlock J n) (hc : pCore 2 J = blockU J)
    (hz : center J = ⊥) {k : ℕ} (hk : k ≤ 3*n) : 2^k ∣ Nat.card G :=
  (pow_dvd_pow 2 hk).trans ((dvd_mul_right _ _).trans (order_dvd h hc hz))

omit [Finite G] in
private theorem core_normalizer (S : Sylow 2 G)
    (hn : (S : Subgroup G) ≤ normalizer (J : Set G)) :
    (S : Subgroup G) ≤ normalizer (J.pCoreIn 2 : Set G) :=
  hn.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))

private theorem normalized_elementary_bound {X : Type*} [Group X] [Finite X]
    (e : G ≃* X) (S : Sylow 2 G) (h : IsL2EvenBlock J n)
    (hc : pCore 2 J = blockU J) (hz : center J = ⊥)
    (hn : (S : Subgroup G) ≤ normalizer (J : Set G)) {k : ℕ}
    (hb : ∀ (P : Sylow 2 X) (E : Subgroup X), IsElementaryAbelian 2 E →
      (P : Subgroup X) ≤ normalizer (E : Set X) → Nat.card E ≤ k) : 2^(2*n) ≤ k := by
  let : IsElementaryAbelian 2 (pCore 2 J) := hc ▸ h.2.1.elementary
  let : IsElementaryAbelian 2 (J.pCoreIn 2) := IsElementaryAbelian.map J.subtype
  have hh := hb (S.mapSurjective e.surjective) ((J.pCoreIn 2).map e.toMonoidHom)
    (IsElementaryAbelian.map e.toMonoidHom)
    ((map_mono (core_normalizer S hn)).trans (le_normalizer_map e.toMonoidHom))
  rwa [card_map_of_injective e.injective,core_card h hc hz] at hh

private theorem quotient_not_dvd_of_local_orders {X : Type*} [Group X] [Finite X]
    (e : G ≃* X) (S : Sylow 2 G) (h : IsL2EvenBlock J n)
    (hn : (S : Subgroup G) ≤ normalizer (J : Set G)) {k : ℕ}
    (hb : ∀ (P : Sylow 2 X) (N : Subgroup X), IsTwoLocal N →
      (P : Subgroup X) ≤ N → ¬ k ∣ Nat.card N) : ¬ k ∣ Nat.card J := by
  let U := J.pCoreIn 2
  have hu : U ≠ ⊥ := fun he => h.2.1.core_ne_bot
    ((map_eq_bot_iff_of_injective _ J.subtype_injective).mp he)
  let N := normalizer (U : Set G)
  have hN : IsTwoLocal N := ⟨U,hu,isPGroup_pCoreIn 2 J,rfl⟩
  have hJN : J ≤ N := J.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hb' := hb (S.mapSurjective e.surjective) (N.map e.toMonoidHom)
    (Theory.Quasithin.isTwoLocal_map e hN) (map_mono (core_normalizer S hn))
  rw [card_map_of_injective e.injective] at hb'
  exact fun hd => hb' (hd.trans (card_dvd_of_le hJN))

private theorem binary_dimension [Group.IsPerfect J]
    (h : IsL2EvenBlock J n) {r : ℕ} (hr : 0 < r)
    (hm : ClassicalGroup.IsPSL G r 2) : 2*n ≤ r := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let a := (e.trans (Atlas.fieldEquivPSL r k)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear hr)
  let f := a.toMonoidHom.comp J.subtype
  let ρ : Representation (ZMod 2) J (BinaryLinear.OuterCyclic.Space r) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f
  have hnt : ∃ j, ρ j ≠ 1 := by
    by_contra! htriv
    have hj : ∀ j : J, j = 1 := by
      intro j
      apply J.subtype_injective
      apply a.injective
      apply LinearEquiv.toLinearMap_injective
      exact (htriv j).trans (htriv 1).symm
    exact h.2.1.core_ne_bot (bot_unique (fun x _ => mem_bot.mpr (hj x)))
  obtain ⟨K,_,_,hK,_,_,⟨m⟩,_⟩ := h.2.2
  let := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  have hd := Representation.SL2.perfect_core_quotient_finrank_bound m.quotientIso ρ hnt
    (by have := h.1; omega) hK
  simpa only [BinaryLinear.OuterCyclic.Space,Module.finrank_fin_fun,Fintype.card_fin] using hd

private theorem not_mathieu24 [Group.IsPerfect J]
    (h : IsL2EvenBlock J 3) (hc : pCore 2 J = blockU J) (hz : center J = ⊥)
    (e : G ≃* Sporadic.Mathieu.M24) : False := by
  let E := (J.pCoreIn 2).map e.toMonoidHom
  let B := J.map e.toMonoidHom
  let : Group.IsPerfect B := Group.IsPerfect.map e.toMonoidHom
  let : IsElementaryAbelian 2 (pCore 2 J) := hc ▸ h.2.1.elementary
  let : IsElementaryAbelian 2 (J.pCoreIn 2) := IsElementaryAbelian.map J.subtype
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map e.toMonoidHom
  apply Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion.no_perfect_large_elementary_normalizer B E
  · exact (map_mono (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))).trans
        (le_normalizer_map e.toMonoidHom)
  · rw [show Nat.card E = Nat.card (J.pCoreIn 2) from card_map_of_injective e.injective,
      core_card h hc hz]
    decide
  · rw [show Nat.card B = Nat.card J from card_map_of_injective e.injective,
      NaturalBlock.card h hc hz]
    norm_num

omit [Finite G] in
private theorem not_janko4_eight (h : IsL2EvenBlock J 3)
    (e : G ≃* Janko4.Model) : False := by
  let B := J.map e.toMonoidHom
  let a := e.subgroupMap J
  obtain ⟨F,_,_,hF,_,_,⟨m⟩,_⟩ := h.2.2
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let d := (QuotientGroup.congr _ _ a.symm (pCore_map_iso 2 a.symm)).trans m.quotientIso
  exact Janko4.no_binary_eight_quotient B hF
    (d.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B)))
    (d.surjective.comp (QuotientGroup.mk'_surjective _))

omit [Finite G] in
private theorem large_core (h : IsL2EvenBlock J n) (ho : Odd n) : 64 ≤ 2^(2*n) := by
  have := h.1
  have := Nat.odd_iff.mp ho
  change 2^6 ≤ 2^(2*n)
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- The actual source catalogue for a normalized odd-degree natural block
has only rank-two containing groups. -/
theorem rank_two [IsQuasisimple G]
    (S : Sylow 2 G) (hl : J ∈ localCComponents S) (hp : J ≠ ⊤)
    (hn : (S : Subgroup G) ≤ normalizer (J : Set G))
    (h : IsL2EvenBlock J n) (hc : pCore 2 J = blockU J) (hz : center J = ⊥)
    (ho : Odd n) (hm : TheoremCModel G) : RankTwoTheoremC G := by
  let := local_perfect hl
  have hn3 : 3 ≤ n := by have := h.1; have := Nat.odd_iff.mp ho; omega
  have hr := rank_bound h hc hz
  have h64 := large_core h ho
  have h512 := two_power_dvd h hc hz (show 9 ≤ 3*n by omega)
  have hd := order_dvd h hc hz
  have no12 (h12 : ¬ 2^12 ∣ Nat.card G) : n = 3 := by
    have hn4 : n < 4 := by
      by_contra! hn4
      exact h12 (two_power_dvd h hc hz (by omega))
    omega
  cases hm with
  | alternating d hdeg iso =>
    obtain ⟨e⟩ := iso
    obtain ⟨hd5,hd8⟩ := hdeg
    let : NeZero d := ⟨by omega⟩
    let : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at h512
    interval_cases d <;> norm_num at h512
  | linear_odd p f hprime hodd hf _ iso =>
    have hb := (ChapterA.Section02.IsTheoremCOddModel.linear_two p f hprime hodd
      (by rcases hf with rfl | rfl <;> decide) iso).twoRank_le_two
    omega
  | three_odd p hprime hodd unitary iso =>
    have hm : ChapterA.Section02.IsTheoremCOddModel G := by
      cases unitary with
      | false => exact .linear_three p hprime hodd iso
      | true => exact .unitary_three p hprime hodd iso
    have hb := hm.twoRank_le_two
    omega
  | rank_one iso =>
    have ht : (⊤ : Subgroup G).IsCComponent :=
      (show IsComponent G ⊤ from ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
    exact (hp (eq_of_bender_containing_component S hl ht le_top
      (iso.of_mulEquiv topEquiv))).elim
  | rank_two iso => exact iso
  | binary_linear d hd iso =>
    have hb := binary_dimension h (by omega : 0 < d) iso
    omega
  | janko_one iso =>
    rw [Nat.card_congr iso.some.toEquiv,Janko1.card_model] at h512
    norm_num at h512
  | sporadic name hne iso =>
    obtain ⟨e⟩ := iso
    cases name with
    | j3 => exact (hne rfl).elim
    | m11 =>
      change G ≃* Sporadic.Mathieu.M11 at e
      rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m11_order] at h512
      norm_num at h512
    | m12 =>
      change G ≃* Sporadic.Mathieu.M12 at e
      rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m12_order] at h512
      norm_num at h512
    | m22 =>
      change G ≃* Sporadic.Mathieu.M22 at e
      have hb := Sporadic.Mathieu.m22_twoRank_le_four
      rw [←primeRank_equiv 2 e] at hb
      omega
    | m23 =>
      change G ≃* Sporadic.Mathieu.M23 at e
      have hb := Sporadic.Mathieu.m23_twoRank_le_four
      rw [←primeRank_equiv 2 e] at hb
      omega
    | hs =>
      change G ≃* Sporadic.LeechRelated.HS.Carrier at e
      have hb := normalized_elementary_bound e S h hc hz hn
        Sporadic.LeechRelated.HS.normal_elementary_card_le_eight
      omega
    | j2 =>
      change G ≃* Sporadic.LeechRelated.J2.Carrier at e
      have hb := normalized_elementary_bound e S h hc hz hn (k := 4) (by
        intro P E he hn
        let := he
        have hep : E ≤ (P : Subgroup Sporadic.LeechRelated.J2.Carrier) :=
          (IsElementaryAbelian.isPGroup 2 E).le_sylow_of_normalized P hn
        have hh := Sporadic.LeechRelated.J2.sylow_normal_elementary_card_le_four P
          (E.subgroupOf (P : Subgroup Sporadic.LeechRelated.J2.Carrier))
          ((normal_subgroupOf_iff_le_normalizer hep).mpr hn)
          (IsElementaryAbelian.subgroupOf hep)
        rwa [Nat.card_congr (subgroupOfEquivOfLe hep).toEquiv] at hh)
      omega
    | m24 =>
      change G ≃* Sporadic.Mathieu.M24 at e
      have he : n = 3 := no12 (by rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m24_order]; norm_num)
      subst n
      exact (not_mathieu24 h hc hz e).elim
    | he =>
      change G ≃* Held.He at e
      have he : n = 3 := no12 (by rw [Nat.card_congr e.toEquiv]; exact Held.not_two_pow_twelve_dvd_card)
      subst n
      apply False.elim
      apply quotient_not_dvd_of_local_orders e S h hn Held.TwoLocalCandidates.not_sixtythree_dvd_card_twoLocal
      rw [NaturalBlock.card h hc hz]
      norm_num
    | ru =>
      change G ≃* Rudvalis.Model at e
      have hn5 : n < 5 := by
        by_contra! hn5
        have hh := two_power_dvd h hc hz (show 15 ≤ 3*n by omega)
        rw [Nat.card_congr e.toEquiv,Rudvalis.model_card] at hh
        norm_num at hh
      have he : n = 3 := by have := Nat.odd_iff.mp ho; omega
      subst n
      apply False.elim
      apply quotient_not_dvd_of_local_orders e S h hn Rudvalis.SylowOvergroups.not_nine_dvd_card_twoLocal
      rw [NaturalBlock.card h hc hz]
      norm_num
    | j4 =>
      change G ≃* Janko4.Model at e
      have hn8 : n < 8 := by
        by_contra! hn8
        have hh := two_power_dvd h hc hz (show 24 ≤ 3*n by omega)
        rw [Nat.card_congr e.toEquiv,Janko4.Cardinality.model_card] at hh
        norm_num at hh
      have hn7 : n ≠ 7 := by
        intro he
        rw [he,Nat.card_congr e.toEquiv,Janko4.Cardinality.model_card] at hd
        norm_num at hd
      have he : n = 3 ∨ n = 5 := by have := Nat.odd_iff.mp ho; omega
      rcases he with rfl | rfl
      · exact (not_janko4_eight h e).elim
      · apply False.elim
        apply quotient_not_dvd_of_local_orders e S h hn
          PointControl.Quasisimple.Other.JankoFour.twoLocal_thirtyOne_free
        rw [NaturalBlock.card h hc hz]
        norm_num
end CFSG.Quasithin.Chapter10.MovingHall.NaturalEmbedding
