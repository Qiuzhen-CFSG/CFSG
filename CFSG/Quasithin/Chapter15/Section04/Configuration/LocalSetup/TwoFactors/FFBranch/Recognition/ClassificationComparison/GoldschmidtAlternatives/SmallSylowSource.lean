module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.GoldschmidtAlternatives.NoncyclicSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.FourSource

/-!
# F.6.18 for a common Sylow subgroup of order at most four

For the literal three-prime quotient and its original Goldschmidt generators,
noncyclic three-core gives rows (1) and (2). In the cyclic case the common Sylow
subgroup has order four; the lower Chapter F source theorem then gives the prime
PSL₂ model, its congruence modulo 24, and both dihedral local groups. This is the
small-Sylow part of Aschbacher–Smith, Theorem F.6.18 (printed pp. 309–310), applied
to the Chapter 15.4 comparison without a classification-output premise.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
variable {κ : GroupClass.{u}} {H : Type u} [Group H] [Finite H]

theorem F618_small_sylow_source
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (S : Type u) [Group S] [Finite S], ChapterA.Section02.TheoremC κ S)
    (hH : IsSQTK κ H) (G₁ G₂ : Subgroup (threePrimeQuotient H))
    (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (hcard : Nat.card (G₁ ⊓ G₂ : Subgroup (threePrimeQuotient H)) ≤ 4) :
    GoldschmidtAlternatives.Alternatives G₁ G₂ := by
  by_cases hc : IsCyclic (pCore 3 (threePrimeQuotient H))
  · have hgt := ChapterF.SourceAssembly.intersection_card_gt_two_of_cyclic_three_core
      (MulEquiv.refl (threePrimeQuotient H)) h hc
    obtain ⟨T, hT⟩ := h.intersection_sylow
    have hfour : Nat.card (G₁ ⊓ G₂ : Subgroup (threePrimeQuotient H)) = 4 := by
      obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
      rw [hT] at hcard hgt ⊢
      have hn2 : n ≤ 2 := by
        apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
        exact hn ▸ hcard
      interval_cases n
      · rw [hn] at hgt
        norm_num at hgt
      · rw [hn] at hgt
        norm_num at hgt
      · exact hn
    obtain ⟨_, _, p, hp, h24, ⟨e⟩⟩ := ChapterF.SourceAssembly.cyclic_four_models
      hA hC hH (MulEquiv.refl _) h hc hfour
    let : Fact p.Prime := ⟨hp⟩
    have hcore : pCore 2 (threePrimeQuotient H) = ⊥ := le_bot_iff.mp
      (ChapterF.twoCore_le_primeToThreeCore.trans
        (ChapterF.Noncyclic.primeToThreeCore_eq_bot_of_quotient (MulEquiv.refl _)).le)
    obtain ⟨hE, hleft, hright⟩ := ChapterF.SourceAssembly.four_intersection_models h hcore hfour
    let U := G₁ ⊓ G₂
    let : IsElementaryAbelian 2 U := hE
    let : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by rw [hfour]; decide)
    let : IsKleinFour U := ⟨hfour, IsElementaryAbelian.exponent_eq_prime⟩
    let : IsKleinFour GoldschmidtAlternatives.E4 :=
      ⟨by simp [GoldschmidtAlternatives.E4, GoldschmidtAlternatives.C],
       by simp [GoldschmidtAlternatives.E4, GoldschmidtAlternatives.C, Monoid.exponent_prod]⟩
    have hm : ClassicalGroup.IsPSL (threePrimeQuotient H) 2 p :=
      ⟨ZMod p, inferInstance, inferInstance, Nat.card_zmod _, ⟨e⟩⟩
    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨p, hp, h24, hm, IsKleinFour.nonempty_mulEquiv, hleft, hright⟩))))
  · exact F618_noncyclic_source hH G₁ G₂ h hc
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
