module

public import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic

/-!
# Intrinsic obstructions for nonswap involutions of S₈

The cycle type of an involution consists of at most four parts of size two.
For three transpositions, an explicit conjugate has product of order seven.
For two or four transpositions, explicit permutations b and g satisfy:
b and ab are conjugate to a, g centralizes a, and b does not commute with
its g-conjugate. These are precisely the rank-one operator obstructions used
by the companion linear module. In particular, the fixed-point-free case
is checked separately; an odd-order product argument does not handle it.

All finite identities are checked by kernel reduction on eight letters.
The configurations supply the involution geometry used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, 13.8.25, printed p.960 (PDF p.977).
-/

public section

namespace Representation.SymmetricEightTransvections
open _root_.Equiv _root_.Equiv.Perm
private abbrev P := Equiv.Perm (Fin 8)

private def rep (n : ℕ) : P :=
  ([swap 0 1, swap 2 3, swap 4 5, swap 6 7].take n).prod

private theorem rep_cycleType (n : Fin 5) :
    (rep n).cycleType = Multiset.replicate n 2 := by
  fin_cases n <;> decide +kernel

private def Obstruction (a : P) : Prop :=
  (∃ b, IsConj a b ∧ (a * b) ^ 7 = 1 ∧ a * b ≠ 1) ∨
  (∃ b g, IsConj a b ∧ IsConj a (a * b) ∧
    Commute g a ∧ ¬ Commute b (g * b * g⁻¹))

private theorem obstruction_map (e : P ≃* P) {a : P}
    (ha : Obstruction a) : Obstruction (e a) := by
  rcases ha with ⟨b, hb, hp, hn⟩ | ⟨b, g, hb, hab, hg, hn⟩
  · left
    refine ⟨e b, e.toMonoidHom.map_isConj hb, ?_, ?_⟩
    · simpa only [map_mul, map_pow, map_one] using congrArg e hp
    · intro h
      apply hn
      apply e.injective
      simpa only [map_mul, map_one] using h
  · right
    refine ⟨e b, e g, e.toMonoidHom.map_isConj hb, ?_, ?_, ?_⟩
    · simpa only [map_mul, MulEquiv.coe_toMonoidHom] using e.toMonoidHom.map_isConj hab
    · exact hg.map e
    · intro h
      apply hn
      apply e.injective
      simpa only [map_mul, map_inv] using h.eq

private theorem obstruction_two : Obstruction (rep 2) := by
  let b : P := swap 0 1 * swap 4 5
  let g : P := swap 0 2 * swap 1 3 * swap 5 6
  right
  refine ⟨b, g, ?_, ?_, ?_, ?_⟩
  · apply isConj_of_cycleType_eq; decide +kernel
  · apply isConj_of_cycleType_eq; decide +kernel
  · unfold Commute SemiconjBy; decide +kernel
  · unfold Commute SemiconjBy; decide +kernel

private theorem obstruction_three : Obstruction (rep 3) := by
  let b : P := swap 1 2 * swap 3 4 * swap 5 6
  left
  refine ⟨b, ?_, ?_, ?_⟩
  · apply isConj_of_cycleType_eq; decide +kernel
  · decide +kernel
  · decide +kernel

private theorem obstruction_four : Obstruction (rep 4) := by
  let b : P := swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7
  let g : P := swap 2 4 * swap 3 5 * swap 6 7
  right
  refine ⟨b, g, ?_, ?_, ?_, ?_⟩
  · apply isConj_of_cycleType_eq; decide +kernel
  · apply isConj_of_cycleType_eq; decide +kernel
  · unfold Commute SemiconjBy; decide +kernel
  · unfold Commute SemiconjBy; decide +kernel

/-- Every nonswap involution in S₈ has either a conjugate with product of
order seven or a transvection-triple centralizer obstruction. -/
theorem involution_obstruction (a : Equiv.Perm (Fin 8))
    (ha : a ≠ 1) (ha2 : a ^ 2 = 1) (has : ¬ a.IsSwap) :
    (∃ b, IsConj a b ∧ (a * b) ^ 7 = 1 ∧ a * b ≠ 1) ∨
    (∃ b g, IsConj a b ∧ IsConj a (a * b) ∧
      Commute g a ∧ ¬ Commute b (g * b * g⁻¹)) := by
  change Obstruction a
  have hc := cycleType_of_pow_prime_eq_one ha2
  have hn : a.cycleType.card ≤ 4 := by
    have hsum := a.sum_cycleType_le
    rw [hc, Multiset.sum_replicate] at hsum
    simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at hsum
    omega
  have hpos := (card_cycleType_pos.mpr ha)
  have hnot : a.cycleType.card ≠ 1 := by
    intro h
    apply has
    rw [isSwap_iff_cycleType, hc, h]
    rfl
  have hrep : IsConj (rep a.cycleType.card) a := by
    apply isConj_of_cycleType_eq
    exact (rep_cycleType ⟨a.cycleType.card, by omega⟩).trans hc.symm
  have hlow : 2 ≤ a.cycleType.card := by omega
  have hbad : Obstruction (rep a.cycleType.card) := by
    interval_cases hn' : a.cycleType.card
    · exact obstruction_two
    · exact obstruction_three
    · exact obstruction_four
  obtain ⟨g, hg⟩ := isConj_iff.mp hrep
  simpa only [MulAut.conj_apply, hg] using obstruction_map (MulAut.conj g) hbad

end Representation.SymmetricEightTransvections
