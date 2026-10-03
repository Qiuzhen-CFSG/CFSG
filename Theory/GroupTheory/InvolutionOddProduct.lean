module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Conjugacy of square-one elements with odd-order product

Two elements whose squares are one are conjugate whenever their product has
odd order. If that order is `2m + 1`, conjugation by the inverse of the
`(m + 1)`st power of the product carries the first element to the second.

This is the elementary dihedral argument used for Glauberman's Suzuki
characterization, Proposition 2.3, specialized to the prime two. The proof
is extracted from the existing private lemma
`xi1115_isConj_of_involutions_odd_product` in
`BenderSuzuki/External/Huppert/XI/theorem_11_15.lean`.
-/

/-- Square-one elements with odd-order product are conjugate. -/
public theorem isConj_of_involutions_odd_product
    {G : Type*} [Group G]
    (t u : G) (htsq : t ^ 2 = 1) (husq : u ^ 2 = 1)
    (hodd : Odd (orderOf (t * u))) :
    IsConj t u := by
  rw [isConj_iff]
  obtain ⟨m, hm⟩ := hodd
  let r : G := t * u
  let k : ℕ := m + 1
  have htinv : t⁻¹ = t := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using htsq
  have huinv : u⁻¹ = u := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using husq
  have htt : t * t = 1 := by simpa [pow_two] using htsq
  have hsem : SemiconjBy t r r⁻¹ := by
    change t * (t * u) = (t * u)⁻¹ * t
    rw [mul_inv_rev, htinv, huinv, ← mul_assoc, htt, one_mul,
      mul_assoc, htt, mul_one]
  have htrk : t * r ^ k = (r ^ k)⁻¹ * t := by
    have hp := hsem.pow_right k
    simpa [inv_pow] using hp.eq
  have hrpow : r ^ (2 * m + 1) = 1 := by
    have hp := pow_orderOf_eq_one r
    simpa [r, hm] using hp
  have htwoK : 2 * k = (2 * m + 1) + 1 := by
    dsimp [k]
    omega
  have hrTwoK : r ^ (2 * k) = r := by
    rw [htwoK, pow_succ, hrpow, one_mul]
  refine ⟨(r ^ k)⁻¹, ?_⟩
  calc
    (r ^ k)⁻¹ * t * ((r ^ k)⁻¹)⁻¹ = (r ^ k)⁻¹ * t * r ^ k := by simp
    _ = (t * r ^ k) * r ^ k := by rw [htrk]
    _ = t * r ^ (2 * k) := by
      rw [mul_assoc, ← pow_add, show k + k = 2 * k by omega]
    _ = t * r := by rw [hrTwoK]
    _ = u := by
      dsimp [r]
      rw [← mul_assoc, htt, one_mul]
