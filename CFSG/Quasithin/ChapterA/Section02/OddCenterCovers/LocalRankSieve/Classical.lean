module
public import CFSG.Quasithin.ChapterA.Section02.OddCenterCovers.LocalRanks
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.SpecificGroups.SU3.FixedFieldTwo
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.SpecificGroups.PSU3.UniversalCover.Kernel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.NumberTheory.BinaryTorusParity
/-!
# The classical leaf of the cubic-cover local-rank sieve

For an actual degree-three special linear or unitary group with cubic center,
the checked local rank calculations exclude every classical model except
SU₃(2ⁿ) with odd n ≥ 3 when the local three-rank is at most one. Center orders
supply the congruences in odd characteristic; the small unitary group over
the binary fixed field is excluded by its solvable projective quotient.

Source: Aschbacher–Smith A.2.12(I.i), printed p.36.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.OddCenterCovers.LocalRankSieve
open Chapter1.Section02.LocalModels
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]

omit [Finite L] in
private theorem unitary_prime_mod_three {q : ℕ} (hq : q.Prime) (ho : Odd q)
    (h : IsSU L 3 q) (hz : Nat.card (center L) = 3) : q % 3 = 2 := by
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h
  have hq2 : 2 < q := by
    have := hq.two_le
    have hne : q ≠ 2 := by rintro rfl; norm_num at ho
    omega
  have hfixed : Nat.card {x : F // J.conj x = x} = q := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj q 1
      (by decide) (by simpa using hcard) (by simpa using hconj)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J q hq2 hcard hfixed
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Group.IsPerfect.ofSurjective (f := J.specialToProjective.comp e.toMonoidHom)
      (J.specialToProjective_surjective.comp e.surjective)
  have hpz : center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
    rcases (inferInstance : (center (ProjectiveSpecialUnitaryMatrixGroup J)).Normal).eq_bot_or_eq_top
      with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht)).elim
  have hzc : Nat.card (center J.specialSubgroup) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).symm.trans hz
  have hkc : Nat.card J.specialToProjective.ker = 3 := by
    rw [J.specialToProjective_ker_eq_center hpz]
    exact hzc
  have hg : Nat.gcd 3 (q + 1) = 3 :=
    (HermitianForm.UniversalCover.card_kernel J hcard hconj).symm.trans hkc
  have hd : 3 ∣ q + 1 := hg ▸ Nat.gcd_dvd_right 3 (q + 1)
  have := Nat.mod_eq_zero_of_dvd hd
  omega

omit [Finite L] in
private theorem not_unitary_two (h : IsSU L 3 2) : False := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Group.IsPerfect.ofSurjective (f := J.specialToProjective.comp e.toMonoidHom)
      (J.specialToProjective_surjective.comp e.surjective)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let : Nontrivial (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [HermitianForm.FixedFieldTwo.card_projective J hcard hconj]
      norm_num)
  exact Group.IsPerfect.not_isSolvable _
    (HermitianForm.FixedFieldTwo.projective_isSolvable J hcard hconj)

theorem classical_of_local_rank_le_one (unitary : Bool) (q : ℕ)
    (hq : CoverParameter unitary q) (hm : IsSLSign L unitary 3 q)
    (hz : Nat.card (center L) = 3) (hl : twoLocalPrimeRank 3 L ≤ 1) :
    ∃ n : ℕ, 3 ≤ n ∧ Odd n ∧ IsSpecialUnitaryModel L 3 (2 ^ n) := by
  cases unitary
  · change IsSL L 3 q at hm
    rcases hq with ⟨n, hn, rfl, hmod⟩ | ⟨hp, ho⟩
    · change 2 ^ n % 3 = 1 at hmod
      have hnE : Even n := by
        have hx := Nat.BinaryTorusParity.two_pow_mod_three n
        have hnm : n % 2 = 0 := by split_ifs at hx <;> simp_all
        exact Nat.even_iff.mpr hnm
      have hr := linear_binary_special_twoLocalPrimeRank_eq_two (by omega) hnE hm
      omega
    · have hmod : q % 3 = 1 := by
        obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
        have hzc : Nat.card (center (SL(3,F))) = 3 :=
          (Nat.card_congr (centerCongr e).toEquiv).symm.trans hz
        rw [Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin, hF] at hzc
        have hd : 3 ∣ q - 1 := hzc ▸ Nat.gcd_dvd_right 3 (q - 1)
        have := Nat.mod_eq_zero_of_dvd hd
        have := hp.two_le
        omega
      have hr := (linear_odd_prime_rank_pair hp ho hmod hm).2
      omega
  · change IsSU L 3 q at hm
    rcases hq with ⟨n, hn, rfl, hmod⟩ | ⟨hp, ho⟩
    · change 2 ^ n % 3 = 2 at hmod
      have hnO : Odd n := by
        have hx := Nat.BinaryTorusParity.two_pow_mod_three n
        have hnm : n % 2 ≠ 0 := by intro he; simp [he] at hx; omega
        exact Nat.odd_iff.mpr (by omega)
      have hn3 : 3 ≤ n := by
        by_contra hh
        have hn1 : n = 1 := by have := Nat.odd_iff.mp hnO; omega
        subst n
        exact not_unitary_two (by simpa using hm)
      exact ⟨n, hn3, hnO, hm⟩
    · have hmod := unitary_prime_mod_three hp ho hm hz
      have hr := (unitary_odd_prime_rank_pair hp ho hmod hm).2
      omega
end CFSG.Quasithin.ChapterA.Section02.OddCenterCovers.LocalRankSieve
