module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveModelsRank
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveModelsQuotient

/-!
# The remaining models in the nonblock prime-rank argument

Combine the full component-quotient classification with the outside-actor
rank restriction. The alternating, odd PSL₂, binary higher-linear and
centerless sporadic rows have rank one at every source torus prime. The
two alternating triple covers do also, and the triple Mathieu cover can
only remain at the prime three. Rank two thus leaves the explicitly
listed Lie models or a classical cubic cover, with the full quotient and
its actual center preserved throughout.

The final dispatch takes only the original secondary data and ambient
source hypotheses. It is checked progress toward A.3.18 and 4.3.12(2),
not the diagonal cubic dichotomy or the four alternatives of 4.3.16.
Those remaining calculations and exceptional-model assembly stay with
qt-d-1222-nonblock-endgame-sieve.
Source: Aschbacher–Smith, A.3.6 and A.3.18, pp.43–45,51–53;
original 4.3.12–16, pp.617–618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- No center hypothesis is needed away from the unique possible cubic center. -/
theorem SecondaryData.component_primeRank_eq_one_of_noncubic_outer_two (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) (hp3 : p ≠ 3)
    (hout : IsPGroup 2 (MulAut.Outer (s.component ⧸ pCore 2 s.component))) :
    primeRank p s.component = 1 :=
  SecondaryData.component_primeRank_eq_one_of_outer_two s D h hp ho hd
    (SecondaryData.componentQuotient_center_coprime s D h hp hp3) hout

/-- A triple Mathieu cover has rank one at every noncubic source prime. -/
theorem SecondaryData.component_primeRank_eq_one_of_noncubic_mathieu_cover (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) (hp3 : p ≠ 3)
    (hm : IsM22Cover (s.component ⧸ pCore 2 s.component)) :
    primeRank p s.component = 1 := by
  let := s.quasisimple
  obtain ⟨_, _, ⟨e⟩⟩ := hm
  have hout := Chapter1.XiEmbedding.OuterModels.m22_outer_isPGroup_two_of_coverage
    Sporadic.Mathieu.m22DesignAutToAut_surjective
  apply SecondaryData.component_primeRank_eq_one_of_noncubic_outer_two s D h hp ho hd hp3
  exact hout.of_injective (MulAut.centralQuotientOuter e) (MulAut.centralQuotientOuter_injective e)

/-- The noncentral quotient alternative is a genuine ternary classical cover
or the cubic Mathieu cover. Neither alternating cover remains. -/
theorem SecondaryData.rank_two_models (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hr : 2 ≤ primeRank p s.component) :
    (center (s.component ⧸ pCore 2 s.component) = ⊥ ∧
      ¬ IsPGroup 2 (MulAut.Outer (s.component ⧸ pCore 2 s.component)) ∧
      ((∃ r : ℕ, r.Prime ∧ Odd r ∧
        (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 r ∨
          ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 r)) ∨
        ClassificationModels.IsBenderModel (s.component ⧸ pCore 2 s.component) ∨
          RankTwoTheoremC (s.component ⧸ pCore 2 s.component))) ∨
      (Nat.card (center (s.component ⧸ pCore 2 s.component)) = 3 ∧
        ((∃ (unitary : Bool) (q : ℕ), CoverParameter unitary q ∧
          IsSLSign (s.component ⧸ pCore 2 s.component) unitary 3 q) ∨
            (p = 3 ∧ IsM22Cover (s.component ⧸ pCore 2 s.component)))) := by
  rcases SecondaryData.componentQuotient_simple_or_threeCover s D h with ⟨_, hz⟩ | ⟨⟨ez⟩, hm⟩
  · exact Or.inl ⟨hz, SecondaryData.outer_not_two_of_rank_two s D h hp ho hd
      (by rw [hz]; simp) hr, SecondaryData.centerless_rank_two_models s D h hp ho hd hz hr⟩
  · refine Or.inr ⟨(Nat.card_congr ez.toEquiv).trans (by simp), ?_⟩
    cases hm with
    | classical unitary q hq hm => exact Or.inl ⟨unitary, q, hq, hm⟩
    | alternating_six hm =>
      have hr1 := SecondaryData.component_primeRank_eq_one_of_alternating_cover s D h hp ho hd
        (Or.inl hm)
      omega
    | alternating_seven hm =>
      have hr1 := SecondaryData.component_primeRank_eq_one_of_alternating_cover s D h hp ho hd
        (Or.inr hm)
      omega
    | mathieu hm =>
      refine Or.inr ⟨?_, hm⟩
      by_contra hp3
      have hr1 := SecondaryData.component_primeRank_eq_one_of_noncubic_mathieu_cover s D h hp ho hd hp3 hm
      omega

/-- Complete rank-one/rank-two dispatch of the proved source-model restrictions.
The remaining Lie and cubic-cover calculations are explicit model branches,
not an assumed A.3.18 conclusion. -/
theorem SecondaryData.prime_rank_model_remainder (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) :
    primeRank p s.component = 1 ∨
      (primeRank p s.component = 2 ∧
        ((center (s.component ⧸ pCore 2 s.component) = ⊥ ∧
          ¬ IsPGroup 2 (MulAut.Outer (s.component ⧸ pCore 2 s.component)) ∧
          ((∃ r : ℕ, r.Prime ∧ Odd r ∧
            (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 r ∨
              ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 r)) ∨
            ClassificationModels.IsBenderModel (s.component ⧸ pCore 2 s.component) ∨
              RankTwoTheoremC (s.component ⧸ pCore 2 s.component))) ∨
          (Nat.card (center (s.component ⧸ pCore 2 s.component)) = 3 ∧
            ((∃ (unitary : Bool) (q : ℕ), CoverParameter unitary q ∧
              IsSLSign (s.component ⧸ pCore 2 s.component) unitary 3 q) ∨
                (p = 3 ∧ IsM22Cover (s.component ⧸ pCore 2 s.component)))))) := by
  rcases SecondaryData.component_primeRank_one_or_two s D h hp ho hd with hr | hr
  · exact Or.inl hr
  · exact Or.inr ⟨hr, SecondaryData.rank_two_models s D h hp ho hd hr.ge⟩
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
