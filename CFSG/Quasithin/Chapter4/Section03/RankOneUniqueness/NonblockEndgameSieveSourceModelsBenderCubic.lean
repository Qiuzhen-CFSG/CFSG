module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceModelsInputs
public import Theory.SpecificGroups.SU3.BinaryCubicRankParity
public import BenderSuzuki.External.Huppert.XI.theorem_3_6

/-!
This additive source variant uses `SecondarySourceData` and preserves the
full quotient and central-cover hypotheses without universal radical movement.

# The cubic-rank-two Bender branch of the nonblock sieve

Binary PSL₂ has odd rank at most one, and Suzuki has order prime to three.
Thus cubic rank two in the Bender catalogue leaves PSU₃. The actual unitary
Sylow calculation excludes even fixed-field degree, leaving odd degree at
least three. All model predicates retain their concrete isomorphisms.

This dispatch feeds the full cubic remainder; the diagonal-actor and local
normalizer inspection remain with qt-d-1222-nonblock-endgame-sieve.
Source: Aschbacher–Smith A.2.4 and A.3.18, pp.33,51–53; original 4.3.12–16,
pp.617–618. Suzuki order primality is Huppert–Blackburn XI.3.6.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- Rank two in a Bender row leaves precisely a unitary model of odd binary degree. -/
theorem SecondarySourceData.bender_cubic_rank_two (s : SecondarySourceData c n)
    (hr : 2 ≤ primeRank 3 s.component)
    (hm : ClassificationModels.IsBenderModel (s.component ⧸ pCore 2 s.component)) :
    ∃ f : ℕ, 3 ≤ f ∧ Odd f ∧
      ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 (2 ^ f) := by
  cases hm with
  | linear f hf hm =>
    have hb := odd_primeRank_le_one hm (by decide : Odd 3)
    omega
  | unitary f hf hm =>
    have ho : Odd f := by
      obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := hm
      apply BenderSuzuki.MatrixGroups.HermitianForm.BinaryCubicRankParity.odd_of_rank_two
        J (by omega) hF hc
      rw [← primeRank_congr 3 e,
        primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup]
      exact hr
    exact ⟨f, by have hh := Nat.odd_iff.mp ho; omega, ho, hm⟩
  | suzuki m hm he =>
    obtain ⟨e⟩ := he
    have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr
      (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).2
    have heq : primeRank 3 s.component = 0 := by
      rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup,
        primeRank_congr 3 e]
      exact hz
    omega

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
