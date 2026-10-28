module

public import Theory.GroupTheory.PrimeRankCubeFree
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import CFSG.KnownSimple.ClassicalModels
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import Theory.Quasithin.LocalRank
/-!
# Odd-prime ranks of the small surviving endpoints

The proved group orders of M₁₁, A₇ and PSU₃(4) have no odd prime cube.
Their ordinary odd-prime ranks, and therefore their two-local ranks, are at
most two. For PSU₃(4), the stored conjugation convention yields the fixed
field order used in the genuine projective unitary order formula.
The source consumer retains the actual quotient local-rank premise; it does
not infer that premise from failure of the ordinary-rank alternative.
Source: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
private theorem cube_free {p : ℕ} (hp : p.Prime) (ho : Odd p)
    {n : ℕ} (hn : n = 7920 ∨ n = 2520 ∨ n = 62400) : ¬ p ^ 3 ∣ n := by
  intro hd
  have hpdiv : p ∣ n := (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  rcases hn with rfl | rfl | rfl
  · have he : 7920 = 2 ^ 4 * 3 ^ 2 * 5 * 11 := by norm_num
    rw [he] at hpdiv
    simp only [hp.dvd_mul, hp.prime.dvd_pow_iff_dvd (by decide : (4 : ℕ) ≠ 0),
      hp.prime.dvd_pow_iff_dvd (by decide : (2 : ℕ) ≠ 0), Nat.prime_dvd_prime_iff_eq hp Nat.prime_two,
      Nat.prime_dvd_prime_iff_eq hp Nat.prime_three,
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11)] at hpdiv
    rcases hpdiv with ((h | h) | h) | h <;> subst p <;> norm_num at *
  · have he : 2520 = 2 ^ 3 * 3 ^ 2 * 5 * 7 := by norm_num
    rw [he] at hpdiv
    simp only [hp.dvd_mul, hp.prime.dvd_pow_iff_dvd (by decide : (3 : ℕ) ≠ 0),
      hp.prime.dvd_pow_iff_dvd (by decide : (2 : ℕ) ≠ 0), Nat.prime_dvd_prime_iff_eq hp Nat.prime_two,
      Nat.prime_dvd_prime_iff_eq hp Nat.prime_three,
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)] at hpdiv
    rcases hpdiv with ((h | h) | h) | h <;> subst p <;> norm_num at *
  · have he : 62400 = 2 ^ 6 * 3 * 5 ^ 2 * 13 := by norm_num
    rw [he] at hpdiv
    simp only [hp.dvd_mul, hp.prime.dvd_pow_iff_dvd (by decide : (6 : ℕ) ≠ 0),
      hp.prime.dvd_pow_iff_dvd (by decide : (2 : ℕ) ≠ 0), Nat.prime_dvd_prime_iff_eq hp Nat.prime_two,
      Nat.prime_dvd_prime_iff_eq hp Nat.prime_three,
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13)] at hpdiv
    rcases hpdiv with ((h | h) | h) | h <;> subst p <;> norm_num at *
variable {Q : Type*} [Group Q] [Finite Q]
/-- The concrete M₁₁ carrier has odd-prime rank at most two. -/
theorem m11_primeRank_le_two {p : ℕ} (hp : p.Prime) (ho : Odd p) (a : Q ≃* Sporadic.Mathieu.M11) :
    primeRank p Q ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  apply primeRank_le_two_of_cube_not_dvd
  rw [Nat.card_congr a.toEquiv,Sporadic.Mathieu.m11_order]
  exact cube_free hp ho (Or.inl rfl)
/-- The actual alternating group A₇ has odd-prime rank at most two. -/
theorem alternating_seven_primeRank_le_two {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (a : Q ≃* alternatingGroup (Fin 7)) : primeRank p Q ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  apply primeRank_le_two_of_cube_not_dvd
  rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup]
  norm_num [Nat.factorial]
  exact cube_free hp ho (Or.inr (Or.inl rfl))
/-- Every literal PSU₃(4) model has odd-prime rank at most two. -/
theorem unitary_four_primeRank_le_two {p : ℕ} (hp : p.Prime) (ho : Odd p) (model : ClassicalGroup.IsPSU Q 3 4) :
    primeRank p Q ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨a⟩⟩ := model
  have hf : Nat.card {x : F // J.conj x = x} = 4 := by
    exact FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2 (by decide) hcard hconj
  have hc := Representation.SU3.BinaryDegree.card_projective J hcard hf
  have hq : Nat.card Q = 62400 := by rw [Nat.card_congr a.toEquiv,hc]; norm_num
  apply primeRank_le_two_of_cube_not_dvd
  rw [hq]
  exact cube_free hp ho (Or.inr (Or.inr rfl))


/-- None of the three small endpoints can have offending odd two-local rank. -/
theorem small_exception_twoLocalRank_le_two {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : Nonempty (Q ≃* Sporadic.Mathieu.M11) ∨
      Nonempty (Q ≃* alternatingGroup (Fin 7)) ∨ ClassicalGroup.IsPSU Q 3 4) :
    twoLocalPrimeRank p Q ≤ 2 := by
  apply (twoLocalPrimeRank_le_primeRank p).trans
  rcases hmodel with hM | hA | hmodel
  · exact m11_primeRank_le_two hp ho hM.some
  · exact alternating_seven_primeRank_le_two hp ho hA.some
  · exact unitary_four_primeRank_le_two hp ho hmodel

end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

/-- The small endpoints are excluded when the actual source quotient has local-rank failure. -/
theorem CounterexampleToTheoremA.centralQuotient_no_small_exception_local_failure
    (h : CounterexampleToTheoremA K G S p)
    (hr : 2 < twoLocalPrimeRank p (S ⧸ center S))
    (hmodel : Nonempty ((S ⧸ center S) ≃* Sporadic.Mathieu.M11) ∨
      Nonempty ((S ⧸ center S) ≃* alternatingGroup (Fin 7)) ∨
      ClassicalGroup.IsPSU (S ⧸ center S) 3 4) : False := by
  have hb := Nonsemisimple.RankTwoSieve.small_exception_twoLocalRank_le_two
    h.2.2.2.2.1 h.2.2.2.2.2.1 hmodel
  omega

end CFSG.Quasithin.ChapterA.Section02
