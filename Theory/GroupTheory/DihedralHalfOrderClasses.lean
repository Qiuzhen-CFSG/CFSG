module

public import Theory.GroupTheory.TwoInvolutionClassOrder

/-!
# Reflection classes under the half-order power

For two involutions `a,b`, put `r = a * b`. Conjugation by a power of `r`
shows that multiplying a reflection by an even power of `r` preserves its
conjugacy class. An odd power exchanges the two reflection classes. Applying
this to `r^(orderOf r / 2)` gives the alternatives modulo four used in
Aschbacher–Smith, A.6.2 (combined manuscript, 1 March 2004, printed p. 64).
The conjugators are constructed in the ambient group, so the exchange result
can be combined with ambient nonconjugacy without any assumption on fusion.
-/

namespace Theory.GroupTheory.DihedralHalfOrderClasses

open Theory.GroupTheory.TwoInvolutionClassOrder
variable {G : Type*} [Group G]

private theorem twist_even {s r : G} (hi : MulAut.conj s r = r⁻¹) (k : ℕ) :
    IsConj s (s * r ^ (2 * k)) := by
  have hm : s * r ^ k = (r ^ k)⁻¹ * s := by
    have hh : MulAut.conj s (r ^ k) = (r ^ k)⁻¹ := by rw [map_pow, hi, inv_pow]
    exact mul_inv_eq_iff_eq_mul.mp hh
  apply isConj_iff.mpr
  refine ⟨(r ^ k)⁻¹, ?_⟩
  calc
    (r ^ k)⁻¹ * s * ((r ^ k)⁻¹)⁻¹ = s * r ^ k * r ^ k := by rw [← hm, inv_inv]
    _ = s * r ^ (2 * k) := by rw [mul_assoc, ← pow_add]; congr 2; omega

private theorem inversions {a b : G} (ha : a * a = 1) (hb : b * b = 1) :
    MulAut.conj a (a * b) = (a * b)⁻¹ ∧ MulAut.conj b (a * b) = (a * b)⁻¹ := by
  have hai : a⁻¹ = a := inv_eq_iff_mul_eq_one.mpr ha
  have hbi : b⁻¹ = b := inv_eq_iff_mul_eq_one.mpr hb
  constructor
  · change a * (a * b) * a⁻¹ = (a * b)⁻¹
    rw [mul_inv_rev, hai, hbi, ← mul_assoc a a b, ha, one_mul]
  · change b * (a * b) * b⁻¹ = (a * b)⁻¹
    rw [mul_inv_rev, hai, hbi, mul_assoc b (a * b) b, mul_assoc a b b, hb, mul_one]

private theorem twist_odd {a b : G} (ha : a * a = 1) (hb : b * b = 1) (k : ℕ) :
    IsConj b (a * (a * b) ^ (2 * k + 1)) ∧ IsConj a (b * (a * b) ^ (2 * k + 1)) := by
  have hi := inversions ha hb
  have heq : a * (a * b) ^ (2 * k + 1) = b * (a * b) ^ (2 * k) := by
    rw [pow_succ', ← mul_assoc, ← mul_assoc a a b, ha, one_mul]
  refine ⟨heq.symm ▸ twist_even hi.2 k, ?_⟩
  have hc : IsConj a (b * (a * b)) := isConj_iff.mpr ⟨b, by
    rw [show b⁻¹ = b from inv_eq_iff_mul_eq_one.mpr hb, mul_assoc]⟩
  have hi2 : MulAut.conj (b * (a * b)) (a * b) = (a * b)⁻¹ := by
    change (b * (a * b)) * (a * b) * (b * (a * b))⁻¹ = _
    calc
      _ = b * (a * b) * b⁻¹ := by group
      _ = _ := hi.2
  have hh := hc.trans (twist_even hi2 k)
  simpa only [pow_succ', mul_assoc] using hh

/-- A product order divisible by four makes the half-order power preserve
both reflection classes. -/
public theorem preserve {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hm : orderOf (a * b) % 4 = 0) :
    IsConj a (a * halfOrder a b) ∧ IsConj b (b * halfOrder a b) := by
  have haa : a * a = 1 := by simpa only [ha, pow_two] using pow_orderOf_eq_one a
  have hbb : b * b = 1 := by simpa only [hb, pow_two] using pow_orderOf_eq_one b
  have he : orderOf (a * b) / 2 = 2 * (orderOf (a * b) / 4) := by omega
  rw [halfOrder_def, he]
  exact ⟨twist_even (inversions haa hbb).1 _, twist_even (inversions haa hbb).2 _⟩

/-- A product order equal to two modulo four makes the half-order power
exchange the reflection classes. -/
public theorem exchange {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hm : orderOf (a * b) % 4 = 2) :
    IsConj b (a * halfOrder a b) ∧ IsConj a (b * halfOrder a b) := by
  have haa : a * a = 1 := by simpa only [ha, pow_two] using pow_orderOf_eq_one a
  have hbb : b * b = 1 := by simpa only [hb, pow_two] using pow_orderOf_eq_one b
  have he : orderOf (a * b) / 2 = 2 * (orderOf (a * b) / 4) + 1 := by omega
  rw [halfOrder_def, he]
  exact twist_odd haa hbb _

end Theory.GroupTheory.DihedralHalfOrderClasses
