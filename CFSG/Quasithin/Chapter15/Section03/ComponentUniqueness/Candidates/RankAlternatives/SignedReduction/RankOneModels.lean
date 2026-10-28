module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.InitialModels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.RankOneModels.Classical
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.RankOneModels.FiniteExclusions
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.EvenModels.G2Ranks
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.EvenModels.TwistedRanks
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.EvenModels.Symplectic
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.SpecificGroups.Triality.ElementaryNine
public import Theory.GroupTheory.PrimeRankZero

/-!
# Restricting the complete 1.1.5 list at three-rank one

This is the rank-one model inspection in the proof of 15.3.37, using the
complete six-constructor input, actual isomorphisms, and trivial odd core.
The characteristic-two survivors have the opposite signed congruences:
PSL₃ requires residue two, whereas PSU₃ requires residue one. Quotient rank
excludes the central two-covers; odd core excludes the alternating triple
covers. The actual small and sporadic carriers provide the remaining rank
obstructions. Simplicity or the PSL₂ projective-line action kills the two-core
of each survivor.

The final theorem supplies the elementary-nine witnesses in the genuine binary
triality carriers, including the smallest field, from the explicit root-word
embedding. Thus the complete model deduction needs only the given 1.1.5 model
alternative, quasisimplicity, trivial odd core and three-rank one.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 1.1.5(3),
printed pp.501–503, and the first rank-one paragraph of 15.3.37, p.1135.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.RankOneModels
open ComponentStructure ClassificationModels Chapter1.Section02.LocalModels
open DiagonalOuter.FieldExclusion.RankOne
variable {K : Type*} [Group K] [Finite K] [IsQuasisimple K]

omit [IsQuasisimple K] in
private theorem suzuki_rank_ne_one {m : ℕ} (hm : 1 ≤ m)
    (hmodel : Nonempty (K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    primeRank 3 K ≠ 1 := by
  obtain ⟨e⟩ := hmodel
  have hcard : ¬ 3 ∣ Nat.card K := by
    rw [Nat.card_congr e.toEquiv]
    exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega)
  have hz : primeRank 3 K = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr hcard
  omega

/-- The complete model restriction with its triality witness family explicit.
`rankOneInitialModel_and_core` supplies this family from the actual carriers. -/
theorem rankOneInitialModel_and_core_of_triality_witnesses
    (htriality : ∀ (f : ℕ) (hf : 0 < f),
      ∃ E : Subgroup (Triality.Standard.BinaryCarrier f hf),
        IsElementaryAbelian 3 E ∧ Nat.card E = 9)
    (alpha : MulAut K) (hmodel : ModelAction115 K alpha)
    (ho : pPrimeCore 2 K = ⊥) (hr : primeRank 3 K = 1) :
    RankOneInitialModel K ∧ pCore 2 K = ⊥ := by
  cases hmodel with
  | lie hs hm _ =>
    let := hs
    refine ⟨?_, core_eq_bot_of_simple⟩
    rcases hm with hb | ht | ⟨n, hn, he⟩
    · cases hb with
      | linear f hf he => exact Or.inl ⟨f, by omega, he⟩
      | unitary f hf he =>
        exact Or.inr (Or.inr (Or.inl ⟨f, by omega,
          unitary_three_residue (by omega) he hr, he⟩))
      | suzuki m hm he => exact (suzuki_rank_ne_one hm he hr).elim
    · cases ht with
      | linear f hf he =>
        exact Or.inr (Or.inl ⟨f, by omega, linear_three_residue he hr, he⟩)
      | symplectic f _ he => exact (rank_ne_one_of_symplectic_even he hr).elim
      | g2 f hf he => exact (rank_ne_one_of_g2_even hf he hr).elim
      | triality f hf he =>
        exact (rank_ne_one_of_triality_of_elementary_nine hf he
          (htriality f (by omega)) hr).elim
      | ree m hm he =>
        obtain ⟨d, ⟨e⟩⟩ := he
        exact (rank_ne_one_of_ree_f4 hm ⟨e.trans d.modelEquiv⟩ hr).elim
      | symplectic_derived he => exact (rank_ne_one_of_symplectic_derived he hr).elim
      | g2_derived he => exact (rank_ne_one_of_g2_derived he hr).elim
      | tits he => exact (rank_ne_one_of_tits he hr).elim
    · have h := binary_linear_rank hn he
      omega
  | two_cover _ _ hm _ =>
    exfalso
    have hu := primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup
    have hl : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by
      rcases hm with hm | hm
      · exact linear_three_even_rank (n := 2) (by decide) hm
      · exact two_le_primeRank_of_g2_even (f := 2) hm
    omega
  | six sigma _ hm => exact (not_alternating_action ho hr (by decide) alpha sigma hm).elim
  | seven sigma _ hm => exact (not_alternating_action ho hr (by decide) alpha sigma hm).elim
  | odd hm _ =>
    rcases hm with hm | ⟨p, hp, he⟩
    · have h := linear_three_ternary_rank hm
      omega
    · exact ⟨Or.inr (Or.inr (Or.inr ⟨p, hp, he⟩)), core_eq_bot_of_linear_two he⟩
  | sporadic name hn he _ => exact (not_sporadic_quotient hr name hn he).elim

/-- The rank-one model inspection in the first paragraph of the proof of
15.3.37. All six alternatives of 1.1.5(3) are accounted for, and the surviving
models have trivial two-core. The triality exclusion uses the genuine
graph-field central quotient, at every positive binary exponent. -/
theorem rankOneInitialModel_and_core
    (alpha : MulAut K) (hmodel : ModelAction115 K alpha)
    (ho : pPrimeCore 2 K = ⊥) (hr : primeRank 3 K = 1) :
    RankOneInitialModel K ∧ pCore 2 K = ⊥ :=
  rankOneInitialModel_and_core_of_triality_witnesses
    Triality.Standard.exists_elementaryAbelian_three_card_nine alpha hmodel ho hr

end CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.RankOneModels
