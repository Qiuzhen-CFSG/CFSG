module

public import Theory.SpecificGroups.Suzuki.EightOuterTori.LinearInput
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.Tactic

/-!
# Order-thirteen matrices and field twists over GF(8)

An order-thirteen matrix in GL(4,8) cannot be conjugate to its image under a
nonidentity automorphism of GF(8). Such a conjugacy would fix its characteristic
polynomial. Every coefficient would then lie in GF(2), since either nonidentity
field automorphism generates the Galois group of order three.

The descended characteristic polynomial has degree four and annihilates the
matrix. Its minimal polynomial over GF(2) also divides X^13 - 1. The thirteenth
cyclotomic polynomial is irreducible of degree twelve over GF(2), because 2 has
order twelve modulo 13. Coprimality therefore forces the minimal polynomial to
divide X - 1, contradicting the matrix's order.

This proves the literal entrywise-map and left-conjugation input used by
`EightOuterTori` for the thirteen-torus branch of Aschbacher–Smith, J.2.10,
printed p.438 (PDF p.449), `refs/quasithin.pdf`; compare GLS3, Theorems 2.5.12
and 6.5.4. No Suzuki centralizer or automizer calculation is used here.
-/

noncomputable section
open Polynomial
namespace BenderSuzuki.MatrixGroups.EightOuterTori
open PFAppendixIII
private abbrev K := BinaryGaloisField 3

/-- A fixed element of either nonidentity field automorphism belongs to GF(2). -/
private theorem fixed_square (σ : K ≃ₐ[ZMod 2] K) (hσ : σ ≠ 1)
    (c : K) (hc : σ c = c) : c ^ 2 = c := by
  let : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 8 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by decide)]
    norm_num
  have hfin : Module.finrank (ZMod 2) K = 3 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    simpa [hcard] using FiniteField.pow_finrank_eq_card 2 K
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
  obtain ⟨i, hi⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2) K).surjective σ
  have hi_lt : i.val < 3 := by simpa [hfin] using i.isLt
  have hφ3 : φ ^ 3 = 1 := by
    have ho := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod 2) K
    have ho3 : orderOf φ = 3 := by simpa [hfin] using ho
    simpa [ho3] using pow_orderOf_eq_one φ
  have hφc : φ c = c := by
    have hi' : φ ^ i.val = σ := hi
    have hcases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases hcases with hi0 | hi1 | hi2
    · exact (hσ (by simpa [hi0] using hi'.symm)).elim
    · simpa [hi1, ← hi'] using hc
    · have hφ2 : (φ ^ 2) c = c := by
        rw [hi2] at hi'
        rw [hi']
        exact hc
      have hh := congrArg φ hφ2
      have hh3 : (φ ^ 3) c = φ c := by
        simpa [pow_succ, pow_two, AlgEquiv.mul_apply] using hh
      simpa [hφ3] using hh3.symm
  simpa [φ, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card] using hφc

/-- An invariant polynomial descends coefficientwise to the prime field. -/
private theorem descends (p : K[X]) (σ : K ≃ₐ[ZMod 2] K)
    (hσ : σ ≠ 1) (hfix : p.map σ.toRingHom = p) :
    ∃ q : (ZMod 2)[X], q.map (algebraMap (ZMod 2) K) = p := by
  classical
  have hlift : p ∈ lifts (algebraMap (ZMod 2) K) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    have hc : σ (p.coeff n) = p.coeff n := by
      simpa using congrArg (fun q : K[X] => q.coeff n) hfix
    have hsq := fixed_square σ hσ (p.coeff n) hc
    have hz : p.coeff n = 0 ∨ p.coeff n = 1 := by
      have hz : p.coeff n * (p.coeff n - 1) = 0 := by
        calc
          _ = p.coeff n ^ 2 - p.coeff n := by ring
          _ = 0 := sub_eq_zero.mpr hsq
      exact (mul_eq_zero.mp hz).imp_right sub_eq_zero.mp
    rcases hz with hz | hz
    · exact ⟨0, by simpa using hz.symm⟩
    · exact ⟨1, by simpa using hz.symm⟩
  exact (mem_lifts p).mp hlift

private theorem cyclotomic_thirteen_irreducible :
    Irreducible (cyclotomic 13 (ZMod 2)) := by
  apply ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (by norm_num : ¬ 2 ∣ 13)
    (dvd_refl _)
  have hu : orderOf (ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 13)) = 12 := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
    · decide
    · intro r hr hrd
      have hr_le : r ≤ 12 := Nat.le_of_dvd (by norm_num) hrd
      interval_cases r <;> try norm_num at hr <;> try norm_num at hrd <;> decide
  rw [hu, natDegree_cyclotomic, Nat.totient_prime (by norm_num : Nat.Prime 13)]

/-- An order-thirteen matrix in GL(4,8) is not conjugate to a nonidentity field twist. -/
public theorem thirteen_twist_separation : ThirteenTwistSeparation := by
  classical
  let : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  intro x g σ hx h
  by_contra hσ
  let M : Matrix (Fin 4) (Fin 4) K := x
  have hconjM : (g : Matrix (Fin 4) (Fin 4) K) *
      M.map σ.toRingHom * (g⁻¹ : Matrix (Fin 4) (Fin 4) K) = M := by
    simpa [M, Matrix.GeneralLinearGroup.map_apply] using congrArg
      (fun z : GL (Fin 4) K => (z : Matrix (Fin 4) (Fin 4) K)) h
  have hchar : Matrix.charpoly (M.map σ.toRingHom) = Matrix.charpoly M := by
    rw [← Matrix.charpoly_units_conj (g : (Matrix (Fin 4) (Fin 4) K)ˣ), hconjM]
  have hfix : M.charpoly.map σ.toRingHom = M.charpoly := by
    rw [← Matrix.charpoly_map]
    exact hchar
  obtain ⟨q, hq⟩ := descends M.charpoly σ hσ hfix
  have hqdeg : q.natDegree = 4 := by
    rw [← natDegree_map_eq_of_injective (algebraMap (ZMod 2) K).injective q,
      hq, Matrix.charpoly_natDegree_eq_dim]
    simp
  have hqne : q ≠ 0 := by
    intro hz
    simp [hz] at hqdeg
  have hqzero : aeval M q = 0 := by
    rw [← aeval_map_algebraMap K M q, hq]
    exact Matrix.aeval_self_charpoly M
  let m := minpoly (ZMod 2) M
  have hmdiv : m ∣ q := minpoly.dvd (ZMod 2) M hqzero
  have hmdeg : m.natDegree ≤ 4 := hqdeg ▸ natDegree_le_of_dvd hmdiv hqne
  have hmne : m ≠ 0 := ne_zero_of_dvd_ne_zero hqne hmdiv
  have hmpow : m ∣ X ^ 13 - 1 := by
    apply minpoly.dvd (ZMod 2) M
    have hxpow : x ^ 13 = 1 := by simpa [hx] using pow_orderOf_eq_one x
    have hMpow : M ^ 13 = 1 := by
      exact congrArg (fun z : GL (Fin 4) K => (z : Matrix (Fin 4) (Fin 4) K)) hxpow
    simp [hMpow]
  have hcop : IsCoprime m (cyclotomic 13 (ZMod 2)) := by
    apply IsCoprime.symm
    apply (Irreducible.coprime_iff_not_dvd cyclotomic_thirteen_irreducible).mpr
    intro hd
    have hle := natDegree_le_of_dvd hd hmne
    have hcycdeg : (cyclotomic 13 (ZMod 2)).natDegree = 12 := by
      rw [natDegree_cyclotomic, Nat.totient_prime (by norm_num : Nat.Prime 13)]
    rw [hcycdeg] at hle
    omega
  have hmlinear : m ∣ X - 1 := by
    apply hcop.dvd_of_dvd_mul_left
    simpa only [cyclotomic_prime_mul_X_sub_one (ZMod 2) 13] using hmpow
  have hMone : M = 1 := by
    obtain ⟨r, hr⟩ := hmlinear
    have he := congrArg (aeval M) hr
    have : M - 1 = 0 := by simpa [m, minpoly.aeval] using he
    exact sub_eq_zero.mp this
  have hxone : x = 1 := Units.ext hMone
  simp [hxone] at hx
end BenderSuzuki.MatrixGroups.EightOuterTori
