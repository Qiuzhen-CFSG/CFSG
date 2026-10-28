module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Tactic

/-!
# Small conjugate products on seven and eight letters

An involution is a product of disjoint transpositions. For two and three
transpositions, explicit even conjugators give products of orders five and
seven respectively. Conjugacy transports these witnesses. Consequently a
bound of four, even when tested only against alternating conjugators,
leaves a single transposition on seven letters, and either a transposition
or four disjoint transpositions on eight letters.

Only the displayed seven- and eight-letter identities are computed. Cycle
types and conjugacy give structural coverage of all involutions.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.11.2(4–5), printed p.364 (PDF p.375), and the proof of 6.2.19,
printed p.691 (PDF p.708).
-/

@[expose] public section

namespace Representation.RankTwo.Symmetric
open _root_.Equiv _root_.Equiv.Perm

private def rep (n k : ℕ) : Perm (Fin (n + 7)) :=
  ([swap 0 1, swap 2 3, swap 4 5, swap 6 7].take k).prod

private def conjugator (n k : ℕ) : Perm (Fin (n + 7)) :=
  if k = 2 then swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4
  else swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4 * swap 4 5 * swap 5 6

private theorem rep_cycleType (n : Fin 2) (k : Fin 5) (hk : 2 * k.val ≤ n.val + 7) :
    (rep n k).cycleType = Multiset.replicate k 2 := by
  fin_cases n <;> fin_cases k <;> revert hk <;> decide +kernel

private theorem certificate (n : Fin 2) (k : Fin 2) :
    (conjugator n (k.val + 2)).sign = 1 ∧
    (rep n (k.val + 2) * (conjugator n (k.val + 2) *
      rep n (k.val + 2) * (conjugator n (k.val + 2))⁻¹)) ^ (2 * k.val + 5) = 1 ∧
    rep n (k.val + 2) * (conjugator n (k.val + 2) *
      rep n (k.val + 2) * (conjugator n (k.val + 2))⁻¹) ≠ 1 := by
  fin_cases n <;> fin_cases k <;> decide +kernel

private theorem obstruction (n : Fin 2) (k : Fin 2) :
    ∃ g ∈ alternatingGroup (Fin (n.val + 7)),
      4 < orderOf (rep n (k.val + 2) * (g * rep n (k.val + 2) * g⁻¹)) := by
  obtain ⟨hs, hp, hn⟩ := certificate n k
  refine ⟨conjugator n (k.val + 2), hs, ?_⟩
  have prime : Nat.Prime (2 * k.val + 5) := by fin_cases k <;> decide
  let : Fact (Nat.Prime (2 * k.val + 5)) := ⟨prime⟩
  rw [orderOf_eq_prime hp hn]
  omega

private theorem obstruction_conjugate {n : ℕ} {a : Perm (Fin n)}
    (ha : ∃ g ∈ alternatingGroup (Fin n), 4 < orderOf (a * (g * a * g⁻¹)))
    (p : Perm (Fin n)) :
    ∃ g ∈ alternatingGroup (Fin n),
      4 < orderOf ((p * a * p⁻¹) * (g * (p * a * p⁻¹) * g⁻¹)) := by
  obtain ⟨g, hg, ho⟩ := ha
  refine ⟨p * g * p⁻¹, ?_, ?_⟩
  · simp only [mem_alternatingGroup, map_mul, map_inv, show g.sign = 1 from hg,
      mul_one, mul_inv_cancel]
  · have he : (p * a * p⁻¹) *
        ((p * g * p⁻¹) * (p * a * p⁻¹) * (p * g * p⁻¹)⁻¹) =
        MulAut.conj p (a * (g * a * g⁻¹)) := by
      simp only [MulAut.conj_apply]
      group
    rw [he, (MulAut.conj p).orderOf_eq]
    exact ho

private theorem cycle_card_ne_two_three (n : Fin 2) (v : Perm (Fin (n.val + 7)))
    (hv : v ^ 2 = 1)
    (hb : ∀ g ∈ alternatingGroup (Fin (n.val + 7)),
      orderOf (v * (g * v * g⁻¹)) ≤ 4) :
    v.cycleType.card ≠ 2 ∧ v.cycleType.card ≠ 3 := by
  have hc := cycleType_of_pow_prime_eq_one hv
  have bad (k : Fin 2) (hk : v.cycleType.card = k.val + 2) : False := by
    have hc' : IsConj (rep n (k.val + 2)) v := by
      apply isConj_of_cycleType_eq
      rw [hc, hk]
      exact rep_cycleType n ⟨k.val + 2, by omega⟩ (by dsimp; omega)
    obtain ⟨p, hp⟩ := isConj_iff.mp hc'
    have hh := obstruction_conjugate (obstruction n k) p
    rw [hp] at hh
    obtain ⟨g, hg, ho⟩ := hh
    exact (not_lt_of_ge (hb g hg)) ho
  exact ⟨fun h => bad 0 h, fun h => bad 1 h⟩

theorem seven_isSwap (v : Perm (Fin 7)) (hv : v ≠ 1) (hv2 : v ^ 2 = 1)
    (hb : ∀ g ∈ alternatingGroup (Fin 7), orderOf (v * (g * v * g⁻¹)) ≤ 4) :
    v.IsSwap := by
  obtain ⟨h2, h3⟩ := cycle_card_ne_two_three 0 v hv2 hb
  have hc := cycleType_of_pow_prime_eq_one hv2
  have hp := card_cycleType_pos.mpr hv
  have hs := v.sum_cycleType_le
  rw [hc, Multiset.sum_replicate] at hs
  simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at hs
  have h1 : v.cycleType.card = 1 := by omega
  rw [isSwap_iff_cycleType, hc, h1]
  rfl

theorem eight_isSwap_or_four (v : Perm (Fin 8)) (hv : v ≠ 1) (hv2 : v ^ 2 = 1)
    (hb : ∀ g ∈ alternatingGroup (Fin 8), orderOf (v * (g * v * g⁻¹)) ≤ 4) :
    v.IsSwap ∨ v.cycleType = {2, 2, 2, 2} := by
  obtain ⟨h2, h3⟩ := cycle_card_ne_two_three 1 v hv2 hb
  have hc := cycleType_of_pow_prime_eq_one hv2
  have hp := card_cycleType_pos.mpr hv
  have hs := v.sum_cycleType_le
  rw [hc, Multiset.sum_replicate] at hs
  simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at hs
  have hd : v.cycleType.card = 1 ∨ v.cycleType.card = 4 := by omega
  rcases hd with hd | hd
  · left; rw [isSwap_iff_cycleType, hc, hd]; rfl
  · right; rw [hc, hd]; rfl

end Representation.RankTwo.Symmetric
