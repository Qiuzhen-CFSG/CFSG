module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveModelsCenter
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveModelsOddTernary
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveModelsCubicRemainder

/-!
# Prime-rank model restrictions after the cubic-cover exclusion

The literal torus and secondary subgroup exclude a cubic quotient center
whenever three divides the torus order. Combining this with the preceding
Lie-model dispatch gives an actual signed projective ternary model, with
the source congruence, in every cubic-rank-two case. At every other source
prime the odd-prime ternary models have rank one, leaving only the explicit
binary Lie models or a classical cubic cover in the rank-two branch.

These applications discharge all premises of the new center obstruction
and model exponent helpers. They do not assert the diagonal action in
4.3.12(2), nor the four local alternatives of 4.3.16. Those remaining
arguments and exceptional-model assembly belong to
qt-d-1222-nonblock-endgame-sieve; final contradiction assembly belongs to
qt-d-1222-nonblock-endgame.
Source: Aschbacher–Smith A.3.18, pp.51–53; original 4.3.12–16, pp.617–618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Chapter1.Section02.LocalModels
open ChapterA.Section03.OddPrime.SourceModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The required center coprimality is proved at every source torus prime. -/
theorem SecondaryData.component_primeRank_eq_one_of_outer_two_at_torus_prime (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hout : IsPGroup 2 (MulAut.Outer (s.component ⧸ pCore 2 s.component))) :
    primeRank p s.component = 1 :=
  SecondaryData.component_primeRank_eq_one_of_outer_two s D h hp ho hd
    (SecondaryData.componentQuotient_center_coprime_of_torus_prime s D h hp ho hd) hout

/-- The cubic rank-two branch has no central-cover alternative. -/
theorem SecondaryData.cubic_rank_two_ternary_models (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2 ^ n - 1) (hr : 2 ≤ primeRank 3 s.component) :
    center (s.component ⧸ pCore 2 s.component) = ⊥ ∧
      ((∃ r : ℕ, r.Prime ∧ Odd r ∧
        (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 r ∨
          ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 r)) ∨
        (∃ f : ℕ, 3 ≤ f ∧ Odd f ∧
          ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 (2 ^ f)) ∨
          (∃ f : ℕ, 2 ≤ f ∧ Even f ∧
            ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 (2 ^ f) ∧
            IsPGLThree ((theta (rootNormalizer c ⧸ pCore 2 (rootNormalizer c))) ⧸
              pPrimeCore 3 (theta (rootNormalizer c ⧸ pCore 2 (rootNormalizer c)))) (2 ^ f))) := by
  rcases SecondaryData.cubic_rank_two_models s D h hd hr with hm | ⟨hz, _⟩
  · exact hm
  · exact (SecondaryData.componentQuotient_center_card_ne_source_prime s D h
      Nat.prime_three (by decide) hd hz).elim

/-- Rank two away from three excludes all odd-prime ternary models and the
Mathieu cubic cover. The remaining full-quotient models are explicit. -/
theorem SecondaryData.noncubic_rank_two_models (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) (hp3 : p ≠ 3)
    (hr : 2 ≤ primeRank p s.component) :
    (center (s.component ⧸ pCore 2 s.component) = ⊥ ∧
      ¬ IsPGroup 2 (MulAut.Outer (s.component ⧸ pCore 2 s.component)) ∧
      (ClassificationModels.IsBenderModel (s.component ⧸ pCore 2 s.component) ∨
        RankTwoTheoremC (s.component ⧸ pCore 2 s.component))) ∨
      (Nat.card (center (s.component ⧸ pCore 2 s.component)) = 3 ∧
        ∃ (unitary : Bool) (q : ℕ), CoverParameter unitary q ∧
          IsSLSign (s.component ⧸ pCore 2 s.component) unitary 3 q) := by
  rcases SecondaryData.rank_two_models s D h hp ho hd hr with ⟨hz, hout, hm⟩ | ⟨hz, hm⟩
  · refine Or.inl ⟨hz, hout, ?_⟩
    rcases hm with ⟨r, hrp, hro, hm⟩ | hm
    · have he := SecondaryData.component_primeRank_eq_one_of_noncubic_odd_ternary
        s D h hp ho hd hp3 hrp hro hz hm
      omega
    · exact hm
  · refine Or.inr ⟨hz, ?_⟩
    rcases hm with hm | ⟨he, _⟩
    · exact hm
    · exact (hp3 he).elim
/-- Cubic rank two gives an actual signed projective ternary model with the
source congruence. The diagonal actor clause remains a separate obligation. -/
theorem SecondaryData.cubic_rank_two_signed_projective_model (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2 ^ n - 1) (hr : 2 ≤ primeRank 3 s.component) :
    ∃ (unitary : Bool) (q : ℕ), SignedCongruence unitary q ∧
      IsPSLSign (s.component ⧸ pCore 2 s.component) unitary 3 q := by
  rcases (SecondaryData.cubic_rank_two_ternary_models s D h hd hr).2 with
    ⟨r, hrp, hro, hm | hm⟩ | ⟨f, _, ho, hm⟩ | ⟨f, _, he, hm, _⟩
  · exact ⟨false, r, SecondaryData.odd_linear_cubic_congruence s D h hd hr hrp hro hm, hm⟩
  · exact ⟨true, r, SecondaryData.odd_unitary_cubic_congruence s D h hd hr hrp hro hm, hm⟩
  · refine ⟨true, 2 ^ f, ?_, hm⟩
    change 2 ^ f % 3 = 2
    rw [Nat.BinaryTorusParity.two_pow_mod_three, Nat.odd_iff.mp ho]
    rfl
  · refine ⟨false, 2 ^ f, ?_, hm⟩
    change 2 ^ f % 3 = 1
    rw [Nat.BinaryTorusParity.two_pow_mod_three, Nat.even_iff.mp he]
    rfl
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
