module

public import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Group
/-!
# An order-three actor on a four-group in S6

Two distinct commuting even involutions in S6 generate a four-group. Any
commuting odd involution extends it to an eight-group. An even element of
order three cycles the four-group and normalizes this eight-group.

Conjugate the first involution to (01)(23). Its centralizer has sixteen
explicit elements; kernel-checked finite calculations supply the actor.
This is the finite local step used to recover Held's alpha from the supplied
A6 in the proof of Lemmas 5.9–5.10, Illinois J. Math. 13 (1969), p.238,
DOI 10.1215/ijm/1256053756.
-/

open Equiv Equiv.Perm Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SixCycler
private def p : Perm (Fin 6) := swap 0 1 * swap 2 3
private def central (i : Fin 16) : Perm (Fin 6) :=
  (swap 0 1) ^ (i.val % 2) * (swap 2 3) ^ (i.val / 2 % 2) *
  (swap 0 2 * swap 1 3) ^ (i.val / 4 % 2) * (swap 4 5) ^ (i.val / 8 % 2)
private def coded (x y z : Fin 6) : Fin 6 → Fin 6 :=
  ![x, p x, y, p y, z, if z = 4 then 5 else 4]
set_option maxRecDepth 10000 in
private theorem coded_complete : ∀ x y z : Fin 6,
    (∀ j, coded x y z (coded x y z j) = j) →
    (∀ j, p (coded x y z j) = coded x y z (p j)) →
    ∃ k : Fin 16, coded x y z = fun j => central k j := by decide +kernel
private theorem central_complete (b : Perm (Fin 6)) (hb : b ^ 2 = 1)
    (hc : Commute p b) : ∃ k : Fin 16, b = central k := by
  have hact (i : Fin 6) : p (b i) = b (p i) := congrArg (fun q : Perm (Fin 6) => q i) hc.eq
  have h1 : b 1 = p (b 0) := (hact 0).symm
  have h3 : b 3 = p (b 2) := (hact 2).symm
  have fixed : ∀ j : Fin 6, p j = j → j = 4 ∨ j = 5 := by decide +kernel
  have h4 := fixed (b 4) (hact 4)
  have h5' := fixed (b 5) (hact 5)
  have h5 : b 5 = if b 4 = 4 then 5 else 4 := by
    have hne : b 4 ≠ b 5 := b.injective.ne (by decide)
    rcases h4 with h4 | h4 <;> rcases h5' with h5' | h5' <;> simp_all
  have he : (fun j => b j) = coded (b 0) (b 2) (b 4) := by
    funext j
    fin_cases j <;> simp [coded, h1, h3, h5]
  obtain ⟨k, hk⟩ := coded_complete (b 0) (b 2) (b 4)
    (by rw [← he]; intro j; exact congrArg (fun q : Perm (Fin 6) => q j) hb)
    (by rw [← he]; exact hact)
  exact ⟨k, Equiv.ext (congrFun (he.trans hk))⟩
-- Small explicit order-three permutations, including both orientations.
private def actor (i : Fin 4) : Perm (Fin 6) := ![
  swap 0 1 * swap 0 2,
  swap 0 2 * swap 0 1,
  swap 0 2 * swap 2 4 * swap 1 3 * swap 3 5,
  swap 2 4 * swap 0 2 * swap 3 5 * swap 1 3] i
set_option maxRecDepth 10000 in
private theorem finite_cycler : ∀ i j : Fin 16,
    (central i) ^ 2 = 1 → sign (central i) = 1 → central i ≠ 1 → central i ≠ p →
    (central j) ^ 2 = 1 → sign (central j) ≠ 1 → Commute (central i) (central j) →
    ∃ k : Fin 4,
      (actor k) ^ 3 = 1 ∧ sign (actor k) = 1 ∧
      (actor k)⁻¹ * p * actor k = p * central i ∧
      (actor k)⁻¹ * central i * actor k = p ∧
      (actor k)⁻¹ * central j * actor k ∈
        ({central j, p * central j, central i * central j, p * central i * central j} : Set _) := by
  simp only [Commute, SemiconjBy, Set.mem_insert_iff, Set.mem_singleton_iff]
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem involution_type (a : Perm (Fin 6)) (ha : a ^ 2 = 1)
    (hne : a ≠ 1) (hs : sign a = 1) : a.cycleType = {2, 2} := by
  have ho : orderOf a = 2 := orderOf_eq_prime ha hne
  obtain ⟨k, hk⟩ := cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hb := a.sum_cycleType_le
  rw [hk] at hb
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hb
  have hb' : k ≤ 2 := by omega
  rw [sign_of_cycleType', hk] at hs
  interval_cases k <;> norm_num at hs
  simpa using hk

public theorem exists_cycler (r q a : Perm (Fin 6))
    (hr : r ^ 2 = 1) (hrne : r ≠ 1) (hrs : sign r = 1)
    (hq : q ^ 2 = 1) (hqne : q ≠ 1) (hqs : sign q = 1) (hqr : q ≠ r)
    (ha : a ^ 2 = 1) (has : sign a ≠ 1)
    (hrq : Commute r q) (hra : Commute r a) (hqa : Commute q a) :
    ∃ b : Perm (Fin 6), b ^ 3 = 1 ∧ sign b = 1 ∧
      b⁻¹ * r * b = r * q ∧ b⁻¹ * q * b = r ∧
      b⁻¹ * a * b ∈ ({a, r * a, q * a, r * q * a} : Set _) := by
  have ht : p.cycleType = {2,2} := by decide +kernel
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr
    ((involution_type r hr hrne hrs).trans ht.symm))
  let f := MulAut.conj g
  have hf : f r = p := hg
  obtain ⟨i, hi⟩ := central_complete (f q)
    (by rw [← map_pow, hq, map_one]) (hf ▸ hrq.map f.toMonoidHom)
  obtain ⟨j, hj⟩ := central_complete (f a)
    (by rw [← map_pow, ha, map_one]) (hf ▸ hra.map f.toMonoidHom)
  have hsign (x : Perm (Fin 6)) : sign (f x) = sign x := by
    simp only [f, MulAut.conj_apply, map_mul, map_inv]
    rw [mul_right_comm, mul_inv_cancel, one_mul]
  obtain ⟨k, hk3, hks, hkr, hkq, hka⟩ := finite_cycler i j
    (by rw [← hi, ← map_pow, hq, map_one]) (by rw [← hi, hsign]; exact hqs)
    (by rw [← hi]; exact fun h => hqne (f.injective (h.trans (map_one f).symm)))
    (by rw [← hi, ← hf]; exact fun h => hqr (f.injective h))
    (by rw [← hj, ← map_pow, ha, map_one]) (by rw [← hj, hsign]; exact has)
    (by rw [← hi, ← hj]; exact hqa.map f.toMonoidHom)
  refine ⟨f.symm (actor k), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hk3, map_one]
  · calc
      _ = sign (f (f.symm (actor k))) := (hsign _).symm
      _ = 1 := by rw [f.apply_symm_apply, hks]
  · apply f.injective
    simpa only [map_mul, map_inv, f.apply_symm_apply, hf, hi] using hkr
  · apply f.injective
    simpa only [map_mul, map_inv, f.apply_symm_apply, hf, hi] using hkq
  · rcases hka with h | h | h | h
    · left
      apply f.injective
      simpa only [map_mul, map_inv, f.apply_symm_apply, hj] using h
    · right; left
      apply f.injective
      simpa only [map_mul, map_inv, f.apply_symm_apply, hf, hj] using h
    · right; right; left
      apply f.injective
      simpa only [map_mul, map_inv, f.apply_symm_apply, hi, hj] using h
    · right; right; right
      apply f.injective
      simpa only [map_mul, map_inv, f.apply_symm_apply, hf, hi, hj, Set.mem_singleton_iff] using h
end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SixCycler
