module

public import Theory.GroupTheory.SylowContainingTwoLocal
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource.ExceptionalOdd.LocalCover
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RankOneFourNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.SylowCenter
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Hall–Janko has no full Sylow pair at five

The actual carrier order forces the odd complement to have order 25. Its
product with a Sylow two-subgroup of order 128 has nontrivial two-core by
the checked GL(n,5) orders for n at most two. The intrinsic Sylow catalogue
puts every normal elementary subgroup in the marked four-group. The order-two
case gives the marked involution centralizer of order 1920; the order-four
case normalizes into the second local of order 1152. Neither admits 25.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511; GLS3 Table 5.3g.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics
open Seed PairNormalizer RankOneFourNormalizer

private abbrev j2Sylow := SecondParabolic.sylow FirstParabolic.card_l₁

private theorem j2_normal_elementary_normalizer_not_twentyfive
    (R : Subgroup s) (hR : R ≠ ⊥) (hn : R.Normal) (he : IsElementaryAbelian 2 R) :
    ¬ 25 ∣ Nat.card (normalizer (R.map s.subtype : Set Carrier)) := by
  let W := R.map s.subtype
  have hWs : W ≤ s := map_subtype_le R
  have hWR : W.subgroupOf s = R := by
    exact comap_map_eq_self_of_injective s.subtype_injective R
  have hWn : (W.subgroupOf s).Normal := hWR.symm ▸ hn
  let := he
  have hWe : IsElementaryAbelian 2 W := IsElementaryAbelian.map s.subtype
  have hWne : W ≠ ⊥ := fun h => hR ((R.map_eq_bot_iff_of_injective s.subtype_injective).mp h)
  have hWfour := normal_elementary_le_four W hWs hWn hWe
  have hd : Nat.card W ∣ 2 ^ 2 := by
    simpa [card_four] using card_dvd_of_le hWfour
  obtain ⟨n, hn2, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hWgt : 1 < Nat.card W := W.one_lt_card_iff_ne_bot.mpr hWne
  interval_cases n
  · exact (hWne (W.eq_bot_of_card_eq (by simpa using hc))).elim
  · have hW2 : Nat.card W = 2 := by simpa using hc
    have hR2 : Nat.card R = 2 := by
      rw [← card_map_of_injective s.subtype_injective]
      exact hW2
    let := hn
    have hRZ := central_of_normal_card_two R hR2
    have hRcenter : R = center s := eq_of_le_of_card_ge hRZ (by rw [SecondParabolic.card_center_s,hR2])
    have hWline : W = zpowers GeneratorPair.FirstFusion.t := by
      change R.map s.subtype = _
      rw [hRcenter,SecondParabolic.center_s]
    change ¬ 25 ∣ Nat.card (normalizer (W : Set Carrier))
    rw [hWline,normalizer_zpowers_eq_centralizer_of_order_two _ SecondParabolic.central_involution_order]
    change ¬ 25 ∣ Nat.card l₁
    rw [FirstParabolic.card_l₁]
    decide
  · have hW4 : Nat.card W = 4 := by simpa using hc
    intro h25
    have hh := h25.trans (card_dvd_of_le (normal_four_normalizer_le W hWs hWn hWe hW4))
    rw [card_p₂] at hh
    norm_num at hh

theorem jankoTwo_no_five_pair (B : Subgroup Carrier) (S : Sylow 2 Carrier)
    (hB : XiOddQuotient 5 B)
    (hperm : (B : Set Carrier) * (S : Set Carrier) = (S : Set Carrier) * (B : Set Carrier)) :
    False := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hB25 : Nat.card B = 25 := by
    rcases hB with ⟨_,hc⟩ | ⟨_,hc,_⟩
    · exact hc
    · have hd := B.card_subgroup_dvd_card
      rw [hc,FirstParabolic.card_carrier] at hd
      norm_num at hd
  have hS128 : Nat.card S = 128 :=
    (Nat.card_congr (S.equiv j2Sylow).toEquiv).trans (SecondParabolic.card_sylow _)
  have hcore : pCore 2 (B ⊔ (S : Subgroup Carrier) : Subgroup Carrier) ≠ ⊥ := by
    apply product_twoCore_ne_bot (d := 2) (t := 6) B S hB.isPGroup S.isPGroup'
      (by decide) hperm (by rw [hB25]; rfl) (by rw [hS128]; norm_num)
    intro n hn
    interval_cases n <;> norm_num [Fin.prod_univ_succ]
  apply no_pair_of_twoCore_of_local_cover j2Sylow _ B S hB hcore
  intro M hM hTM
  obtain ⟨R,hR,hn,he,hRM⟩ := exists_normal_elementary_normalizer_of_sylow_le j2Sylow hM hTM
  rw [hRM]
  exact j2_normal_elementary_normalizer_not_twentyfive R hR hn he

variable {κ : GroupClass} {J : Type*} [Group J] [Finite J]
    {D B : Subgroup J} {S : Sylow 2 J}

theorem not_jankoTwo
    (hA : OddCartan.AmbientInput κ D B S 5)
    (hB : SourceTransport.PairAction 5 (S : Subgroup J) B)
    (e : D ≃* Carrier) : False := by
  let : D.Normal := hA.normal
  obtain ⟨U,_,hU,hperm⟩ := exists_model_sylow_pair S hA.inside hB.oddComplement hA.permutes e
  exact jankoTwo_no_five_pair _ U hU hperm
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
