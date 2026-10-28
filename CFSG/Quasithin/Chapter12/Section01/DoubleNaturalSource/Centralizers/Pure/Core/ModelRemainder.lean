module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.Sieve
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ElementaryBound
public import Theory.SpecificGroups.Held.CentralCovers.OddCenter
public import Theory.Mathieu.SchurMultipliers.SourceCovers

/-!
# The three remaining pure-point component models

The literal component has a central involution and quotient two-rank at
least six. Intrinsic model bounds exclude the small-rank rows, including
J₂. The proved M₂₄ and Held central-cover results exclude those rows using
the original central involution, leaving exactly G₂(4), Rudvalis and J₄.
The actual component quotient and the full original automorphism condition
are retained. Core.Complete applies this to the original pure point.

Source: Aschbacher--Smith 12.1.6, printed p.791, and 1.1.5(3), pp.501--503.
The imported carrier and covering calculations preserve their attribution.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels

private theorem j2_rank : primeRank 2 Sporadic.LeechRelated.J2.Carrier ≤ 4 := by
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let := hE
  exact Sporadic.LeechRelated.J2.ElementarySixteenFusion.elementary_card_le_sixteen E

private theorem sporadic_rank_le_four (name : SporadicName)
    (hm24 : name ≠ .m24) (hj3 : name ≠ .j3) (hj4 : name ≠ .j4)
    (hhe : name ≠ .he) (hru : name ≠ .ru) : primeRank 2 name.Carrier ≤ 4 := by
  cases name with
  | m11 =>
    exact (Theory.GroupTheory.primeRank_le_of_injective 2 MulAut.conj
      (MulAut.conj_injective_of_center_eq_bot Sporadic.Mathieu.m11_center_eq_bot)).trans
      (Sporadic.Mathieu.m11_automorphism_twoRank_le_two.trans (by decide))
  | m12 => exact Sporadic.Mathieu.m12_twoRank_le_three.trans (by decide)
  | m22 => exact Sporadic.Mathieu.m22_twoRank_le_four
  | m23 => exact Sporadic.Mathieu.m23_twoRank_le_four
  | m24 => exact (hm24 rfl).elim
  | j2 => exact j2_rank
  | j3 => exact (hj3 rfl).elim
  | j4 => exact (hj4 rfl).elim
  | hs => exact Sporadic.LeechRelated.HS.twoRank_le_four
  | he => exact (hhe rfl).elim
  | ru => exact (hru rfl).elim

/-- Central involutions and rank at least six leave only three literal models. -/
theorem model115_of_central_involution_of_six_le_rank
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (a : MulAut K) (hm : ModelAction115 K a)
    (hc : center K = pCore 2 K) (v : K) (hv : v ∈ center K) (hv2 : orderOf v = 2)
    (hr : 6 ≤ primeRank 2 (K ⧸ pCore 2 K)) :
    (IsG2At (K ⧸ pCore 2 K) 4 ∧ a ∈ (MulAut.conj (G := K)).range) ∨
    ((Nonempty ((K ⧸ pCore 2 K) ≃* Rudvalis.Model) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) ∧ TwoCentralInner a) := by
  rcases model115_of_central_involution a hm v hv hv2 with ⟨_,hm,ha⟩ | ⟨name,hj3,hm,ha⟩
  · rcases hm with hm | hm
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      have hq : primeRank 2 (K ⧸ pCore 2 K) = 4 := by
        rw [primeRank_equiv 2 e]
        exact Matrix.PSL3Even.two_rank F (n := 2) (by decide) hF
      omega
    · exact Or.inl ⟨hm,ha⟩
  · by_cases hj4 : name = .j4
    · subst name
      exact Or.inr ⟨Or.inr hm,ha⟩
    by_cases hru : name = .ru
    · subst name
      exact Or.inr ⟨Or.inl hm,ha⟩
    have hvord : orderOf (⟨v,hv⟩ : center K) = 2 :=
      (orderOf_injective (center K).subtype (center K).subtype_injective ⟨v,hv⟩).symm.trans hv2
    have hd : 2 ∣ Nat.card (center K) := hvord ▸ orderOf_dvd_natCard (⟨v,hv⟩ : center K)
    have hhe : name ≠ .he := by
      intro he
      subst name
      obtain ⟨e⟩ := hm
      have ho := Held.CentralCovers.odd_center
        ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans e⟩
      exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hd)
    have hm24 : name ≠ .m24 := by
      intro he
      subst name
      obtain ⟨e⟩ := hm
      have hz := Sporadic.Mathieu.SchurMultipliers.m24_center_eq_bot_of_centralQuotientEquiv
        ((QuotientGroup.quotientMulEquivOfEq hc).trans e)
      have hv1 : v = 1 := mem_bot.mp (hz ▸ hv)
      simp [hv1] at hv2
    obtain ⟨e⟩ := hm
    let : Finite name.Carrier := Finite.of_equiv (K ⧸ pCore 2 K) e.toEquiv
    have hb := sporadic_rank_le_four name hm24 hj3 hj4 hhe hru
    rw [←primeRank_equiv 2 e] at hb
    omega
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

