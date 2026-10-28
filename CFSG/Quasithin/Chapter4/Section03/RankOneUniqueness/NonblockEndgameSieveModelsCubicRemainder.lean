module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveModelsRemainder
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveModelsLieCubic
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveModelsSplitPrimes
public import Theory.SpecificGroups.PSL3.BinaryCubicRankParity
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveModelsBenderCubic

/-!
# The ternary remainder at a cubic source torus prime

Dispatch every constructor of the source rank-two catalogue. Cubic residual
calculations exclude symplectic, G₂, genuine triality and Ree. The outer-two
calculation handles the small derived and Tits endpoints. In the Bender
catalogue only odd-degree PSU₃ remains. The binary PSL₃ branch has even degree
and an actual PGL₃ model for the reduced ambient theta quotient.

The final theorem retains the full quotient and its cubic center alternative.
It leaves odd-prime ternary models and the classical/Mathieu cubic covers
explicit. It does not assert the diagonal-actor conclusion of A.3.18 or the
four-row inspection of 4.3.16. Their discharge and final exceptional-model
assembly remain with qt-d-1222-nonblock-endgame-sieve.
Source: Aschbacher–Smith A.2.4, A.3.6, A.3.18, pp.33,43–45,51–53;
original 4.3.12–16, pp.617–618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Chapter1.Section02.LocalModels
open ChapterA.Section03.OddPrime.SourceModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The small derived symplectic, derived G₂ and Tits endpoints have rank
one at every source torus prime. -/
theorem SecondaryData.component_primeRank_eq_one_of_small_rank_two (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hm : Nonempty ((s.component ⧸ pCore 2 s.component) ≃*
        commutator (ClassicalGroup.PSp 2 (ZMod 2))) ∨
      Nonempty ((s.component ⧸ pCore 2 s.component) ≃*
        commutator (Atlas.G2.Model (ZMod 2))) ∨
      Nonempty ((s.component ⧸ pCore 2 s.component) ≃* Tits.ParrottGroup)) :
    primeRank p s.component = 1 := by
  rcases hm with hm | hm | hm
  all_goals obtain ⟨e⟩ := hm
  · exact SecondaryData.component_primeRank_eq_one_of_alternating s D h hp ho hd (by decide : 5 ≤ 6)
      (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
  · apply SecondaryData.component_primeRank_eq_one_of_outer_two s D h hp ho hd
    · rw [Nat.card_congr (centerCongr e).toEquiv,
        Theory.SpecificGroups.g2_derived_two_center_eq_bot]
      simp
    · exact Theory.SpecificGroups.BinaryComponentResidual.g2_outer_two.of_equiv
        (MulAut.outerCongr e).symm
  · apply SecondaryData.component_primeRank_eq_one_of_outer_two s D h hp ho hd
    · rw [Nat.card_congr (centerCongr e).toEquiv, Tits.parrottGroup_center_eq_bot]
      simp
    · exact Tits.OuterOddSubgroups.parrott_outer_isPGroup.of_equiv (MulAut.outerCongr e).symm

/-- At a cubic source prime only binary PSL₃ remains from the source
rank-two catalogue. This handles all eight constructors of that catalogue. -/
theorem SecondaryData.centerless_cubic_rank_two_models (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2 ^ n - 1)
    (hz : center (s.component ⧸ pCore 2 s.component) = ⊥)
    (hr : 2 ≤ primeRank 3 s.component) :
    (∃ r : ℕ, r.Prime ∧ Odd r ∧
      (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 r ∨
        ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 r)) ∨
      ClassificationModels.IsBenderModel (s.component ⧸ pCore 2 s.component) ∨
        (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 (2 ^ f)) := by
  rcases SecondaryData.centerless_rank_two_models s D h Nat.prime_three (by decide) hd hz hr
    with hm | hm | hm
  · exact Or.inl hm
  · exact Or.inr (Or.inl hm)
  cases hm with
  | linear f hf hm => exact Or.inr (Or.inr ⟨f, hf, hm⟩)
  | symplectic f hf hm => exact (SecondaryData.not_symplectic_of_three_dvd s D h hd hf hm).elim
  | g2 f hf hm => exact (SecondaryData.not_g2_of_three_dvd s D h hd hf hm).elim
  | triality f hf hm => exact (SecondaryData.not_triality_of_three_dvd s D h hd hf hm).elim
  | ree m hm he => exact (SecondaryData.not_ree_of_three_dvd_of_center_bot s D h hd hz hm he).elim
  | symplectic_derived hm =>
    have hr1 := SecondaryData.component_primeRank_eq_one_of_small_rank_two s D h Nat.prime_three
      (by decide) hd (Or.inl hm)
    omega
  | g2_derived hm =>
    have hr1 := SecondaryData.component_primeRank_eq_one_of_small_rank_two s D h Nat.prime_three
      (by decide) hd (Or.inr (Or.inl hm))
    omega
  | tits hm =>
    have hr1 := SecondaryData.component_primeRank_eq_one_of_small_rank_two s D h Nat.prime_three
      (by decide) hd (Or.inr (Or.inr hm))
    omega

/-- The surviving binary linear row has even field degree and the actual
PGL theta quotient in the reduced ambient group. -/
theorem SecondaryData.binary_linear_cubic_rank_two (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2 ^ n - 1) (hr : 2 ≤ primeRank 3 s.component)
    {f : ℕ} (hf : 1 ≤ f)
    (hm : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 (2 ^ f)) :
    2 ≤ f ∧ Even f ∧
      IsPGLThree ((theta (rootNormalizer c ⧸ pCore 2 (rootNormalizer c))) ⧸
        pPrimeCore 3 (theta (rootNormalizer c ⧸ pCore 2 (rootNormalizer c)))) (2 ^ f) := by
  have heven : Even f := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    apply Matrix.PSL3.BinaryCubicRankParity.even_of_rank_two hF
    rw [← primeRank_congr 3 e,
      primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup]
    exact hr
  have hlarge : 2 ≤ f := by have hh := Nat.even_iff.mp heven; omega
  exact ⟨hlarge, heven, SecondaryData.binary_linear_reduced_theta_isPGL s D h
    (by omega) hd ((Nat.BinaryTorusParity.three_dvd_sub_one_iff f).mpr heven) hm⟩

/-- The full cubic-rank-two quotient retains its possible cubic center.
Its centerless branch consists only of ternary linear and unitary models. -/
theorem SecondaryData.cubic_rank_two_models (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2 ^ n - 1) (hr : 2 ≤ primeRank 3 s.component) :
    (center (s.component ⧸ pCore 2 s.component) = ⊥ ∧
      ((∃ r : ℕ, r.Prime ∧ Odd r ∧
        (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 r ∨
          ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 r)) ∨
        (∃ f : ℕ, 3 ≤ f ∧ Odd f ∧
          ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 (2 ^ f)) ∨
          (∃ f : ℕ, 2 ≤ f ∧ Even f ∧
            ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 (2 ^ f) ∧
            IsPGLThree ((theta (rootNormalizer c ⧸ pCore 2 (rootNormalizer c))) ⧸
              pPrimeCore 3 (theta (rootNormalizer c ⧸ pCore 2 (rootNormalizer c)))) (2 ^ f)))) ∨
      (Nat.card (center (s.component ⧸ pCore 2 s.component)) = 3 ∧
        ((∃ (unitary : Bool) (q : ℕ), CoverParameter unitary q ∧
          IsSLSign (s.component ⧸ pCore 2 s.component) unitary 3 q) ∨
            IsM22Cover (s.component ⧸ pCore 2 s.component))) := by
  rcases SecondaryData.rank_two_models s D h Nat.prime_three (by decide) hd hr with
    ⟨hz, _, _⟩ | ⟨hz, hm | ⟨_, hm⟩⟩
  · refine Or.inl ⟨hz, ?_⟩
    rcases SecondaryData.centerless_cubic_rank_two_models s D h hd hz hr with
      hm | hm | ⟨f, hf, hm⟩
    · exact Or.inl hm
    · exact Or.inr (Or.inl (SecondaryData.bender_cubic_rank_two s hr hm))
    · obtain ⟨hf2, heven, hpgl⟩ := SecondaryData.binary_linear_cubic_rank_two s D h hd hr hf hm
      exact Or.inr (Or.inr ⟨f, hf2, heven, hm, hpgl⟩)
  · exact Or.inr ⟨hz, Or.inl hm⟩
  · exact Or.inr ⟨hz, Or.inr hm⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
