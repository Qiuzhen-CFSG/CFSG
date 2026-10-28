module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels.ClassicalParameters.ComparisonInputs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels.ClassicalParameters.OddQuotients
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.FactorPosition.SylowModel
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.Projective
public import Theory.SpecificGroups.SU3.EvenTwoRank
public import Theory.SpecificGroups.Suzuki.TwoRank
public import Theory.SpecificGroups.SL2.DefiningRank
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# Odd degree-three projective groups are not Bender groups

The actual Sylow two-subgroups of PSL₃(p) and PSU₃(p), for an odd prime p,
are semidihedral or wreathed, so their elementary abelian two-rank is at most
two. The root groups in PSL₂(2ⁿ) and PSU₃(2ⁿ) force n ≤ 2. In the Bender
range this leaves the field order four: their orders divide 60 and equal
62400, respectively. Neither order admits the defining-prime cube supplied
by the odd degree-three root group. The concrete Suzuki matrix group has
two-rank 2m + 1 ≥ 3 and is excluded directly.

All comparisons use the supplied multiplicative equivalences. In particular,
unitary form transport keeps the stored Frobenius and the field of order p².
Simplicity and perfectness are not needed for this exclusion.

Source: Aschbacher–Smith, A.3.6(2), printed p.43; F.9.18(4), pp.325–326;
and the parameter comparison in 13.8.17, p.953 (PDF p.970). The Sylow
presentations are A.3.21(b), p.55; the concrete even-family calculations
are the imported Huppert II.6.14, II.10.12 and Huppert–Blackburn XI.3 results.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition
namespace CFSG.Quasithin.Chapter13.Section08.Components.CoverModels.ClassicalParameters
variable {S : Type*} [Group S] [Finite S]

private theorem odd_sylow_shape {p : ℕ} [Fact p.Prime] (ho : Odd p)
    {unitary : Bool} (h : IsPSLSign S unitary 3 p) (T : Sylow 2 S) :
    Stellmacher.IsSemidihedralGroup T ∨ ABG.IsWreathedGroup T := by
  cases unitary with
  | false => exact isPSL_sylow_shape ho h T
  | true =>
    obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h
    obtain ⟨P, ⟨ep⟩⟩ := projectiveUnitary_sylow_equiv J p hcard hconj
      (T.mapSurjective (f := e.toMonoidHom) e.surjective)
    let et : T ≃* P := (e.subgroupMap (T : Subgroup S)).trans ep
    rcases ChapterA.Section03.su3_sylow_shape p ho P with hs | ⟨n, hw⟩
    · exact Or.inl (ABG.semidihedral_equiv et.symm hs)
    · exact Or.inr ⟨n, ABG.wreathed_equiv et.symm hw⟩

/-- The two-rank bound holds for both actual odd-prime projective models. -/
theorem odd_projective_two_rank_le {p : ℕ} (hp : p.Prime) (ho : Odd p)
    {unitary : Bool} (h : IsPSLSign S unitary 3 p) : primeRank 2 S ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  let T : Sylow 2 S := Classical.choice inferInstance
  rw [T.primeRank_eq]
  apply (primeRank_le_iff_elementary_card_le T).mpr
  intro E hE
  exact (ABG.rank_two_and_cyclic_center_of_sylow_shape (odd_sylow_shape ho h T)).2.1 E hE

private theorem even_linear_exponent_le {n : ℕ}
    (h : ClassicalGroup.IsPSL S 2 (2 ^ n)) : n ≤ primeRank 2 S := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact Matrix.SpecialLinearGroup.fieldExponent_le_primeRank_of_projective_injective
    hcard e.symm.toMonoidHom e.symm.injective

private theorem even_unitary_two_rank {n : ℕ} (hn : 0 < n)
    (h : ClassicalGroup.IsPSU S 3 (2 ^ n)) : primeRank 2 S = n := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_surjective e e.surjective
  rw [primeRank_equiv 2 e]
  exact HermitianForm.EvenTwoRank.two_rank J hn hcard hconj

omit [Finite S] in
private theorem linear_four_card_dvd (h : ClassicalGroup.IsPSL S 2 4) :
    Nat.card S ∣ 62400 := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  have hc := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  rw [← Nat.card_congr e.toEquiv, hcard] at hc
  have hd : Nat.card S ∣ 60 := by
    use Nat.card (center (Matrix.SpecialLinearGroup (Fin 2) F))
    simpa using hc.symm
  exact hd.trans (by norm_num)

omit [Finite S] in
private theorem unitary_four_card (h : ClassicalGroup.IsPSU S 3 4) :
    Nat.card S = 62400 := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h
  have hf : Nat.card {x : F // J.conj x = x} = 4 := by
    exact FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2 (by decide) hcard hconj
  obtain ⟨f⟩ := exists_projectiveEquiv J 4 hcard hf
  obtain ⟨_, _, _, _, _, _, _, _, hc, _⟩ :=
    BenderSuzuki.External.huppert_II_10_12 (standardForm J) 4 hcard hf rfl
  rw [Nat.card_congr (e.trans f).toEquiv]
  norm_num at hc ⊢
  exact hc

private theorem odd_cube_not_dvd_bender_small {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    ¬ p ^ 3 ∣ 62400 := by
  intro hd
  have hpd : p ∣ 2 ^ 6 * 3 * 5 ^ 2 * 13 := by
    norm_num
    exact (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  have hcases : 2 = p ∨ 3 = p ∨ 5 = p ∨ 13 = p := by
    rcases hp.dvd_mul.mp hpd with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · exact Or.inl ((Nat.prime_two.dvd_iff_eq hp.ne_one).mp (hp.dvd_of_dvd_pow h))
        · exact Or.inr (Or.inl ((Nat.prime_three.dvd_iff_eq hp.ne_one).mp h))
      · exact Or.inr (Or.inr (Or.inl
          (((by norm_num : Nat.Prime 5).dvd_iff_eq hp.ne_one).mp (hp.dvd_of_dvd_pow h))))
    · exact Or.inr (Or.inr (Or.inr
        (((by norm_num : Nat.Prime 13).dvd_iff_eq hp.ne_one).mp h)))
  rcases hcases with rfl | rfl | rfl | rfl
  · exact ho.not_two_dvd_nat (dvd_refl 2)
  all_goals norm_num at hd

/-- All three Bender alternatives are excluded, with no additional model premises. -/
theorem oddBenderComparison (S : Type*) [Group S] [Finite S] : OddBenderComparison S := by
  intro unitary p hp ho _ h hb
  have hrank := odd_projective_two_rank_le hp ho h
  have hcube := prime_cube_dvd_card hp h
  cases hb with
  | linear n hn he =>
    have heq : n = 2 := by have := even_linear_exponent_le he; omega
    subst n
    exact odd_cube_not_dvd_bender_small hp ho (hcube.trans (linear_four_card_dvd he))
  | unitary n hn he =>
    have heq : n = 2 := by rw [even_unitary_two_rank (by omega) he] at hrank; omega
    subst n
    exact odd_cube_not_dvd_bender_small hp ho (by rwa [unitary_four_card he] at hcube)
  | suzuki m hm he =>
    obtain ⟨e⟩ := he
    rw [primeRank_equiv 2 e, suzuki_two_rank m (by omega)] at hrank
    omega
end CFSG.Quasithin.Chapter13.Section08.Components.CoverModels.ClassicalParameters
