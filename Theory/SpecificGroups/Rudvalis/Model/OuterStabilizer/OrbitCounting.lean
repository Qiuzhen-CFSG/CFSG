module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Orbit counting for the Tits subgroup in the Rudvalis action

A group of order 17971200 whose proper subgroups have index at least 1600
has a fixed point in every action on 4060 points. Otherwise there are at most
two orbits. One orbit would have size 4060, which does not divide the group
order; two orbit sizes, both at least 1600 and dividing that order, cannot
sum to 4060. The finite arithmetic check is verified by the Lean kernel.

This elementary reduction is motivated by the degree-4060 action in
GLS3, Table 5.3r, printed p.279 (`refs/KGroup/GLS3/Chapter5(sec3-).tex`).
The minimum-index bound remains an explicit hypothesis here.
-/

namespace Rudvalis.OuterStabilizer
open MulAction

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem divisor_pair : ∀ n : Fin 4061,
    1600 ≤ n.val → 1600 ≤ 4060 - n.val → n.val ∣ 17971200 → ¬ (4060 - n.val) ∣ 17971200 := by
  decide +kernel

private theorem sum_ne_4060 {m n : ℕ} (hm : 1600 ≤ m) (hmdiv : m ∣ 17971200)
    (hn : 1600 ≤ n) (hndiv : n ∣ 17971200) : m + n ≠ 4060 := by
  intro h
  have hmle : m < 4061 := by omega
  exact divisor_pair ⟨m, hmle⟩ hm (show 1600 ≤ 4060 - m by omega) hmdiv
    (by simpa [show 4060 - m = n by omega] using hndiv)

/-- A group of Tits order with no proper subgroup of index below 1600
has a fixed point in every action of degree 4060. -/
public theorem exists_fixed_point_of_order_of_min_index {K X : Type*} [Group K] [Finite K] [MulAction K X] [Finite X]
    (hcard : Nat.card K = 17971200)
    (hmin : ∀ L : Subgroup K, L ≠ ⊤ → 1600 ≤ L.index)
    (hX : Nat.card X = 4060) : ∃ x : X, ∀ k : K, k • x = x := by
  classical
  let := Fintype.ofFinite X
  let Q := orbitRel.Quotient K X
  let := Fintype.ofFinite Q
  let d (q : Q) := Fintype.card (orbit K q.out)
  have hsum : ∑ q : Q, d q = 4060 := by
    rw [← Fintype.card_sigma, ← Fintype.card_congr (selfEquivSigmaOrbits K X)]
    simpa only [Nat.card_eq_fintype_card] using hX
  by_contra hn
  have hlarge (q : Q) : 1600 ≤ d q := by
    have hproper : stabilizer K q.out ≠ ⊤ := by
      intro he
      apply hn
      exact ⟨q.out, fun k => show k • q.out = q.out from
        (show k ∈ stabilizer K q.out by rw [he]; trivial)⟩
    simpa only [index_stabilizer, Set.ncard_eq_toFinset_card', Set.toFinset_card, d,
      Nat.card_eq_fintype_card] using hmin _ hproper
  have hdiv (q : Q) : d q ∣ 17971200 := by
    have ht := (stabilizer K q.out).index_dvd_card
    rw [hcard, index_stabilizer] at ht
    simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_card, d, Nat.card_eq_fintype_card] using ht
  have hbound : Fintype.card Q * 1600 ≤ 4060 := by
    calc
      _ = ∑ _q : Q, 1600 := by simp
      _ ≤ ∑ q : Q, d q := Finset.sum_le_sum fun q _ => hlarge q
      _ = _ := hsum
  have hqpos : 0 < Fintype.card Q := by
    by_contra h
    have hz : Fintype.card Q = 0 := by omega
    have hi := Fintype.card_eq_zero_iff.mp hz
    have hzsum : ∑ q : Q, d q = 0 := by simp
    omega
  have hcases : Fintype.card Q = 1 ∨ Fintype.card Q = 2 := by omega
  rcases hcases with hq | hq
  · obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hq
    have heq : d q = 4060 := by simpa [hq] using hsum
    have hd := hdiv q
    rw [heq] at hd
    exact (by decide : ¬4060 ∣ 17971200) hd
  · obtain ⟨q, r, hqr, hq⟩ := Finset.card_eq_two.mp hq
    have heq : d q + d r = 4060 := by simpa [hq, hqr] using hsum
    exact sum_ne_4060 (hlarge q) (hdiv q) (hlarge r) (hdiv r) heq

end Rudvalis.OuterStabilizer
