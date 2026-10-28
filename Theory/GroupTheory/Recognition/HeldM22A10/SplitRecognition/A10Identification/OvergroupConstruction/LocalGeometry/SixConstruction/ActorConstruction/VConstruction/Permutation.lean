module

public import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Group

/-!
# The second actor in the marked symmetric group

Normalize the central involution of the marked dihedral group to (01)(23).
Its involutory centralizer elements have sixteen explicit representatives.
Eight explicit order-three permutations cover the admissible markings. The
condition separating d from a*x removes the other central involution choice.
Every finite calculation is checked by the kernel, and the final theorem
transports the actor back through the actual conjugating permutation.

The centralizer coding argument follows the project's `SixCycler` module;
this calculation includes the additional inversion and centralization required
for Held 4.1. Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, printed p.232.
-/

open Equiv Equiv.Perm Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.VConstruction
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

private def actor (i : Fin 8) : Perm (Fin 6) := ![
  swap 0 1 * swap 1 3, swap 0 1 * swap 1 2,
  swap 1 2 * swap 2 3, swap 1 3 * swap 3 2,
  swap 0 4 * swap 4 3 * swap 1 5 * swap 5 2,
  swap 0 3 * swap 3 5 * swap 1 2 * swap 2 4,
  swap 0 4 * swap 4 2 * swap 1 5 * swap 5 3,
  swap 0 2 * swap 2 4 * swap 1 3 * swap 3 5] i
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxSize 32768 in
private theorem finite_actor : ∀ i j k : Fin 16,
    (central i) ^ 2 = 1 → sign (central i) ≠ 1 →
    (central j) ^ 2 = 1 → sign (central j) = 1 →
    central i * central j * central i * central j = p →
    (central k) ^ 2 = 1 → sign (central k) ≠ 1 →
    Commute (central i) (central k) → Commute (central j) (central k) →
    (central i).cycleType ≠ (p * central k).cycleType →
    ∃ n : Fin 8, (actor n) ^ 3 = 1 ∧
      (actor n)⁻¹ * p * actor n = p * central j ∧
      (actor n)⁻¹ * central j * actor n = p ∧
      central i * actor n * central i = (actor n)⁻¹ ∧
      Commute (actor n) (central k) := by
  simp only [Commute, SemiconjBy]
  intro i
  fin_cases i <;> decide +kernel

public theorem even_involution_cycleType (a : Perm (Fin 6)) (ha : a ^ 2 = 1)
    (hne : a ≠ 1) (hs : sign a = 1) : a.cycleType = {2, 2} :=
  involution_type a ha hne hs

public theorem exists_permutation_actor (a b d x : Perm (Fin 6))
    (ha : a ^ 2 = 1) (hane : a ≠ 1) (has : sign a = 1)
    (hb : b ^ 2 = 1) (hbs : sign b = 1)
    (hd : d ^ 2 = 1) (hds : sign d ≠ 1)
    (hx : x ^ 2 = 1) (hxs : sign x ≠ 1)
    (hab : Commute a b) (had : Commute a d) (hax : Commute a x)
    (hdx : Commute d x) (hbx : Commute b x)
    (hdi : d * b * d * b = a) (hnot : ¬ IsConj d (a * x)) :
    ∃ v : Perm (Fin 6), v ^ 3 = 1 ∧ v⁻¹ * a * v = a * b ∧
      v⁻¹ * b * v = a ∧ d * v * d = v⁻¹ ∧ Commute v x := by
  have ht : p.cycleType = {2, 2} := by decide +kernel
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr
    ((involution_type a ha hane has).trans ht.symm))
  let f := MulAut.conj g
  have hf : f a = p := hg
  have hsign (y : Perm (Fin 6)) : sign (f y) = sign y := by
    simp only [f, MulAut.conj_apply, map_mul, map_inv]
    rw [mul_right_comm, mul_inv_cancel, one_mul]
  obtain ⟨i, hi⟩ := central_complete (f d)
    (by rw [← map_pow, hd, map_one]) (hf ▸ had.map f.toMonoidHom)
  obtain ⟨j, hj⟩ := central_complete (f b)
    (by rw [← map_pow, hb, map_one]) (hf ▸ hab.map f.toMonoidHom)
  obtain ⟨k, hk⟩ := central_complete (f x)
    (by rw [← map_pow, hx, map_one]) (hf ▸ hax.map f.toMonoidHom)
  have hn : (central i).cycleType ≠ (p * central k).cycleType := by
    intro h
    apply hnot
    have hh : IsConj (f d) (f (a * x)) := by
      apply isConj_iff_cycleType_eq.mpr
      simpa only [map_mul, hf, hi, hk] using h
    obtain ⟨z, hz⟩ := isConj_iff.mp hh
    refine isConj_iff.mpr ⟨f.symm z, ?_⟩
    simpa only [map_mul, map_inv, f.symm_apply_apply] using congrArg f.symm hz
  obtain ⟨n, hn3, hna, hnb, hnd, hnx⟩ := finite_actor i j k
    (by rw [← hi, ← map_pow, hd, map_one]) (by rw [← hi, hsign]; exact hds)
    (by rw [← hj, ← map_pow, hb, map_one]) (by rw [← hj, hsign]; exact hbs)
    (by rw [← hi, ← hj, ← map_mul, ← map_mul, ← map_mul, hdi, hf])
    (by rw [← hk, ← map_pow, hx, map_one]) (by rw [← hk, hsign]; exact hxs)
    (by rw [← hi, ← hk]; exact hdx.map f.toMonoidHom)
    (by rw [← hj, ← hk]; exact hbx.map f.toMonoidHom) hn
  refine ⟨f.symm (actor n), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hn3, map_one]
  · apply f.injective
    simpa only [map_mul, map_inv, f.apply_symm_apply, hf, hj] using hna
  · apply f.injective
    simpa only [map_mul, map_inv, f.apply_symm_apply, hf, hj] using hnb
  · apply f.injective
    simpa only [map_mul, map_inv, f.apply_symm_apply, hi] using hnd
  · apply Commute.of_map f.injective
    simpa only [f.apply_symm_apply, hk] using hnx
end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.VConstruction
