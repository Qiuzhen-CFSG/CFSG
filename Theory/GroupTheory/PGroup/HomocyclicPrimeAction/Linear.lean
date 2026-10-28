module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Nat.Choose.Dvd

/-!
# Prime-order linear maps on homocyclic planes

For a prime `p > 3`, a matrix `A` over `ZMod (p²)` satisfying `A^p = 1`
has `p • (A - 1) = 0`. Reducing modulo `p` makes `A - 1` nilpotent;
the two-dimensional kernel bound makes its square zero. Thus over `ZMod (p²)`
the displacement square is divisible by `p`, its fourth power is zero,
and its square is killed by `p`. Prime binomial divisibility in
`((A - 1) + 1)^p` then kills every term except `1 + p • (A - 1)`.

The linear-map corollary fixes all `p`-multiples, ready for transport to
the omega subgroup of a homocyclic group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, proof of Lemma A.1.30, printed p.27.
-/

open scoped BigOperators

namespace HomocyclicPrimeAction

private theorem binomial_displacement {R : Type*} [Ring R]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (d : R)
    (h4 : d ^ 4 = 0) (h2 : d ^ 2 * (p : R) = 0)
    (horder : (d + 1) ^ p = 1) : d * (p : R) = 0 := by
  have hterm (k : ℕ) (hk : k ∈ Finset.range (p + 1)) (hk01 : k ∉ ({0, 1} : Finset ℕ)) :
      d ^ k * 1 ^ (p - k) * (p.choose k : R) = 0 := by
    have hk0 : k ≠ 0 := by simpa using fun h => hk01 (by simp [h])
    have hk1 : k ≠ 1 := by simpa using fun h => hk01 (by simp [h])
    have hkp : k ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    simp only [one_pow, mul_one]
    by_cases hkeq : k = p
    · rw [hkeq, pow_eq_zero_of_le (by omega : 4 ≤ p) h4, zero_mul]
    · obtain ⟨b, hb⟩ := hp.dvd_choose_self hk0 (lt_of_le_of_ne hkp hkeq)
      rw [hb, Nat.cast_mul, ← mul_assoc]
      have hpow : d ^ k * (p : R) = 0 := by
        calc
          d ^ k * (p : R) = d ^ (k - 2) * (d ^ 2 * (p : R)) := by
            rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ k)]
          _ = 0 := by rw [h2, mul_zero]
      rw [hpow, zero_mul]
  have hs : ∑ k ∈ Finset.range (p + 1), d ^ k * 1 ^ (p - k) * (p.choose k : R) =
      1 + d * (p : R) := by
    rw [← Finset.sum_subset (s₁ := ({0, 1} : Finset ℕ)) (by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> simp [hp.pos]) hterm]
    simp
  have h := (Commute.one_right d).add_pow p
  rw [horder, hs] at h
  exact (add_left_cancel (a := (1 : R)) (by simpa using h.symm))

private theorem matrix_nilpotent_sq {K : Type*} [Field K]
    (M : Matrix (Fin 2) (Fin 2) K) (k : ℕ) (hk : M ^ k = 0) : M ^ 2 = 0 := by
  apply Matrix.toLin'.injective
  rw [map_zero, Matrix.toLin'_pow]
  apply LinearMap.ext
  intro x
  have hh := Module.End.ker_pow_le_ker_pow_finrank (Matrix.toLin' M) k
  have hx : x ∈ LinearMap.ker ((Matrix.toLin' M) ^ k) := by
    rw [← Matrix.toLin'_pow, hk, map_zero]
    simp
  have hx' := hh hx
  simpa only [Module.finrank_fin_fun, LinearMap.mem_ker, LinearMap.zero_apply] using hx'

private theorem scalar_factor_of_reduction_zero {p : ℕ} [Fact p.Prime] (z : ZMod (p ^ 2))
    (hz : ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p) z = 0) :
    ∃ y : ZMod (p ^ 2), z = (p : ZMod (p ^ 2)) * y := by
  have hd : p ∣ z.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at hz
    exact hz
  obtain ⟨k, hk⟩ := hd
  refine ⟨k, ?_⟩
  rw [← ZMod.natCast_zmod_val z, hk, Nat.cast_mul]

/-- The displacement of a rank-two matrix whose order divides `p` is killed by `p`. -/
public theorem matrix_prime_smul_sub_one {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (A : Matrix (Fin 2) (Fin 2) (ZMod (p ^ 2))) (hA : A ^ p = 1) :
    (p : ZMod (p ^ 2)) • (A - 1) = 0 := by
  let : CharP (Matrix (Fin 2) (Fin 2) (ZMod p)) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
      have h := congrArg (algebraMap (ZMod p) (Matrix (Fin 2) (Fin 2) (ZMod p)))
        (ZMod.natCast_self p)
      simpa only [map_natCast, map_zero] using h)
  let r := ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)
  let D := A - 1
  have hbar : (r.mapMatrix D) ^ p = 0 := by
    dsimp [D]
    rw [map_sub, map_one, sub_pow_char_of_commute p (Commute.one_right _),
      ← map_pow, hA, map_one, one_pow, sub_self]
  have hbar2 : r.mapMatrix (D ^ 2) = 0 := by
    rw [map_pow]
    exact matrix_nilpotent_sq _ p hbar
  have hfac : ∃ C : Matrix (Fin 2) (Fin 2) (ZMod (p ^ 2)),
      D ^ 2 = (p : ZMod (p ^ 2)) • C := by
    have hf (i j : Fin 2) := scalar_factor_of_reduction_zero ((D ^ 2) i j)
      (congrFun (congrFun hbar2 i) j)
    choose C hC using hf
    exact ⟨C, Matrix.ext hC⟩
  obtain ⟨C, hC⟩ := hfac
  have hz : (p : ZMod (p ^ 2)) * p = 0 := by
    rw [← Nat.cast_mul, ← pow_two]
    exact ZMod.natCast_self _
  have htwo : (p : ZMod (p ^ 2)) • D ^ 2 = 0 := by
    rw [hC, smul_smul, hz, zero_smul]
  have hfour : D ^ 4 = 0 := by
    rw [show D ^ 4 = D ^ 2 * D ^ 2 by simp only [← pow_add], hC,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hz, zero_smul]
  have horder : (D + 1) ^ p = 1 := by simpa only [D, sub_add_cancel] using hA
  have htwo' : D ^ 2 * (p : Matrix (Fin 2) (Fin 2) (ZMod (p ^ 2))) = 0 := by
    rw [← Nat.cast_comm]
    simpa only [Algebra.smul_def, map_natCast] using htwo
  have h := binomial_displacement (Fact.out : p.Prime) hp D hfour htwo' horder
  rw [← Nat.cast_comm] at h
  simpa only [Algebra.smul_def, map_natCast] using h

/-- The displacement of a linear map of order dividing `p` on `(Z/p²)²` is killed by `p`. -/
public theorem linear_prime_smul_sub_one {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (L : Module.End (ZMod (p ^ 2)) (Fin 2 → ZMod (p ^ 2))) (hL : L ^ p = 1) :
    (p : ZMod (p ^ 2)) • (L - 1) = 0 := by
  let e := LinearMap.toMatrixAlgEquiv' (R := ZMod (p ^ 2)) (n := Fin 2)
  have hA : (e L) ^ p = 1 := by rw [← map_pow, hL, map_one]
  have h := matrix_prime_smul_sub_one hp (e L) hA
  apply e.injective
  simpa only [map_smul, map_sub, map_one, map_zero] using h

/-- A linear map of order dividing `p` on `(Z/p²)²` fixes every `p`-multiple. -/
public theorem linear_fixes_prime_multiples {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (L : Module.End (ZMod (p ^ 2)) (Fin 2 → ZMod (p ^ 2))) (hL : L ^ p = 1)
    (x : Fin 2 → ZMod (p ^ 2)) : L (p • x) = p • x := by
  have h := LinearMap.congr_fun (linear_prime_smul_sub_one hp L hL) x
  change (p : ZMod (p ^ 2)) • (L x - x) = 0 at h
  rw [smul_sub, sub_eq_zero, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul] at h
  simpa only [map_nsmul] using h

end HomocyclicPrimeAction
