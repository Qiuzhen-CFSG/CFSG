module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels.ClassicalParameters.ComparisonInputs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels.ClassicalParameters.OddQuotients
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.FactorPosition.SylowModel
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.Projective
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.SpecificGroups.G2Even.TwoRank
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.AtlasPort.LinearGroups.G2.Order

/-!
# Odd degree-three models versus even rank-two families

The genuine semidihedral or wreathed Sylow presentations bound the two-rank
of both PSL₃(p) and PSU₃(p) by two. The unitary transport retains the field
of order p² and its p-power conjugation. The even-field rank formulas exclude
PSL₃(2ⁿ), Sp₄(2ⁿ)′ and G₂(2ⁿ)′ for n ≥ 2.

At n = 1, the defining-prime cube divides the odd model's order, whereas the
orders of the actual binary carriers divide 168, 720 and 12096 respectively.
Their common multiple 60480 has no prime cube divisor at a prime at least
five. This uses subgroup divisibility for the genuine commutator carriers,
without identifying a binary derived group with its full group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6(2),
printed p.43; F.9.18(4), pp.325–326; and the comparison in 13.8.17, p.953
(PDF p.970). The Sylow presentations are the intrinsic A.3.21(b) calculation.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
open CFSG.Quasithin.ChapterA.Section03
namespace CFSG.Quasithin.Chapter13.Section08.Components.CoverModels.ClassicalParameters

variable {S : Type*} [Group S] [Finite S]

private theorem odd_projective_rank_le_two {p : ℕ} (hp : p.Prime) (ho : Odd p)
    {unitary : Bool} (h : IsPSLSign S unitary 3 p) : primeRank 2 S ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  let T : Sylow 2 S := Classical.choice inferInstance
  have hshape : Stellmacher.IsSemidihedralGroup T ∨ ABG.IsWreathedGroup T := by
    cases unitary with
    | false => exact isPSL_sylow_shape ho h T
    | true =>
      obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h
      obtain ⟨P, ⟨ep⟩⟩ := UnitaryPosition.projectiveUnitary_sylow_equiv J p hcard hconj
        (T.mapSurjective (f := e.toMonoidHom) e.surjective)
      let et : T ≃* P := (e.subgroupMap (T : Subgroup S)).trans ep
      rcases su3_sylow_shape p ho P with hP | ⟨k, hP⟩
      · exact Or.inl (ABG.semidihedral_equiv et.symm hP)
      · exact Or.inr ⟨k, ABG.wreathed_equiv et.symm hP⟩
  rw [T.primeRank_eq]
  apply (primeRank_le_iff_elementary_card_le T).mpr
  simpa only [show (2 : ℕ) ^ 2 = 4 from rfl] using
    (ABG.rank_two_and_cyclic_center_of_sylow_shape hshape).2.1

private theorem large_prime_cube_not_dvd {p : ℕ} (hp : p.Prime) (hlarge : 5 ≤ p) :
    ¬ p ^ 3 ∣ 60480 := by
  intro hd
  have hpd : p ∣ 2 ^ 6 * 3 ^ 3 * 5 * 7 := by
    norm_num
    exact (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  have hcases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    simpa only [hp.dvd_mul,
      hp.prime.dvd_pow_iff_dvd (by decide : 6 ≠ 0),
      hp.prime.dvd_pow_iff_dvd (by decide : 3 ≠ 0),
      Nat.prime_dvd_prime_iff_eq hp Nat.prime_two,
      Nat.prime_dvd_prime_iff_eq hp Nat.prime_three,
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7), or_assoc] using hpd
  rcases hcases with rfl | rfl | rfl | rfl
  · omega
  · omega
  · norm_num at hd
  · norm_num at hd

private theorem not_even_linear_three {p n : ℕ} (hp : p.Prime) (ho : Odd p)
    (hlarge : 5 ≤ p) {unitary : Bool} (h : IsPSLSign S unitary 3 p)
    (hn : 1 ≤ n) : ¬ ClassicalGroup.IsPSL S 3 (2 ^ n) := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  have hr := odd_projective_rank_le_two hp ho h
  rw [primeRank_equiv 2 e, Matrix.PSL3Even.two_rank F (by omega) hF] at hr
  have hn1 : n = 1 := by omega
  have hc := Matrix.PSL3.LinearThree.card_projective_mul_scalar F
  rw [← Nat.card_congr e.toEquiv, hF, hn1] at hc
  norm_num at hc
  have hd := prime_cube_dvd_card hp h
  rw [hc] at hd
  exact large_prime_cube_not_dvd hp hlarge (hd.trans (by norm_num))

private theorem not_even_symplectic_four {p n : ℕ} (hp : p.Prime) (ho : Odd p)
    (hlarge : 5 ≤ p) {unitary : Bool} (h : IsPSLSign S unitary 3 p)
    (hn : 1 ≤ n) : ¬ Models.IsSp4DerivedAt S (2 ^ n) := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  by_cases hn2 : 2 ≤ n
  · have hr := odd_projective_rank_le_two hp ho h
    rw [primeRank_equiv 2 e,
      Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derived_rank hF hn2] at hr
    omega
  · have hn1 : n = 1 := by omega
    have hd := prime_cube_dvd_card hp h
    rw [Nat.card_congr e.toEquiv] at hd
    have hd' := hd.trans (commutator (Matrix.symplecticGroup (Fin 2) F)).card_subgroup_dvd_card
    rw [Theory.SpecificGroups.SymplecticFour.card_sp F, hF, hn1] at hd'
    norm_num at hd'
    exact large_prime_cube_not_dvd hp hlarge (hd'.trans (by norm_num))

private theorem not_even_g2 {p n : ℕ} (hp : p.Prime) (ho : Odd p)
    (hlarge : 5 ≤ p) {unitary : Bool} (h : IsPSLSign S unitary 3 p)
    (hn : 1 ≤ n) : ¬ Models.IsG2DerivedAt S (2 ^ n) := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  by_cases hn2 : 2 ≤ n
  · have hr := odd_projective_rank_le_two hp ho h
    rw [primeRank_equiv 2 e, Atlas.G2.EvenTwoRank.derived_two_rank F hn2 hF] at hr
    omega
  · have hn1 : n = 1 := by omega
    have hd := prime_cube_dvd_card hp h
    rw [Nat.card_congr e.toEquiv] at hd
    have hd' := hd.trans (commutator (Atlas.G2.Model F)).card_subgroup_dvd_card
    rw [Atlas.G2.card_Model, hF, hn1] at hd'
    norm_num at hd'
    exact large_prime_cube_not_dvd hp hlarge (hd'.trans (by norm_num))

/-- Odd-prime degree-three projective groups at primes at least five cannot
be any of the even rank-two carriers, including the binary derived groups. -/
theorem oddRankTwoComparison (S : Type*) [Group S] [Finite S] :
    OddRankTwoComparison S := by
  intro unitary p hp ho hlarge h n hn
  exact ⟨not_even_linear_three hp ho hlarge h hn,
    not_even_symplectic_four hp ho hlarge h hn, not_even_g2 hp ho hlarge h hn⟩

end CFSG.Quasithin.Chapter13.Section08.Components.CoverModels.ClassicalParameters
