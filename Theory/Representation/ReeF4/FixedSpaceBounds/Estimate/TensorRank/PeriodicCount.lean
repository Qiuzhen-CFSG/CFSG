module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.CyclicOrder
public import Theory.Representation.ReeF4.BinaryDegree.PeriodicProduct

/-!
# Counting large factors in an exceptional Frobenius period

Multiplication by two permutes the odd cyclic index set. After this numerical
reindexing, shift by `2*s` becomes period `s`. Each block of length `s` then
contains a large factor, so the total contains at least `(2*m+1)/s` of them.
Only the sum of indicator functions is reindexed here; no tensor action or
fixed subspace is replaced.

Source: GLS3, Corollary 2.8.6(b) and Remark 2.8.8; the counting step used with
Guralnick--Malle, *Classification of 2F-modules, II*, Corollary 2.11(a).
-/

public section

namespace ReeF4.FixedSpaceEstimate

open BinaryDegree.ExceptionalTensor

private theorem sum_range_mul_of_periodic {a : ℕ → ℕ} {s : ℕ}
    (ha : Function.Periodic a s) (t : ℕ) :
    (∑ i ∈ Finset.range (s * t), a i) = t * ∑ i ∈ Finset.range s, a i := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Nat.succ_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Nat.cast_id, Nat.mul_comm, Nat.add_comm] using ha.nat_mul t i

private theorem sum_range_cast (m : ℕ) (a : ZMod (2 * m + 1) → ℕ) :
    (∑ i ∈ Finset.range (2 * m + 1), a (i : ZMod (2 * m + 1))) =
      ∑ i : ZMod (2 * m + 1), a i := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv (ZMod.finEquiv (2 * m + 1)).toEquiv _ _ (fun i => by
    congr 1
    exact ZMod.natCast_zmod_val (ZMod.finEquiv (2 * m + 1) i))

private theorem sum_ordinaryIndex (m : ℕ) (a : ZMod (2 * m + 1) → ℕ) :
    (∑ i ∈ Finset.range (2 * m + 1), a (2 * (i : ZMod (2 * m + 1)))) =
      ∑ i : ZMod (2 * m + 1), a i := by
  rw [sum_range_cast m (fun i => a (2 * i))]
  exact Fintype.sum_equiv (ordinaryIndex m) _ _ (fun _ => by rw [ordinaryIndex_apply])

/-- Every repeated ordinary-Frobenius block contains a large exceptional factor. -/
theorem periodic_large_count_ge (m s d : ℕ) (hs : 0 < s) (hsn : s ∣ 2 * m + 1)
    (a : ZMod (2 * m + 1) → ℕ)
    (hlarge : ∃ i, d ≤ a i)
    (hshift : ∀ i, a (i + 2 * (s : ZMod (2 * m + 1))) = a i) :
    (2 * m + 1) / s ≤
      ∑ i ∈ Finset.range (2 * m + 1), if d ≤ a (i : ZMod (2 * m + 1)) then 1 else 0 := by
  let b : ZMod (2 * m + 1) → ℕ := fun i => if d ≤ a i then 1 else 0
  let c : ℕ → ℕ := fun i => b (2 * (i : ZMod (2 * m + 1)))
  have hc : Function.Periodic c s :=
    periodic_of_exceptional_shift m s b (fun i => by dsimp [b]; rw [hshift])
  have heq : (∑ i ∈ Finset.range (2 * m + 1), b (i : ZMod (2 * m + 1))) =
      ∑ i ∈ Finset.range (2 * m + 1), c i := by
    exact (sum_range_cast m b).trans (sum_ordinaryIndex m b).symm
  obtain ⟨j, hj⟩ := hlarge
  obtain ⟨i, hi⟩ := (ordinaryIndex m).surjective j
  have hci : c i.val = 1 := by
    dsimp [c, b]
    rw [ZMod.natCast_zmod_val, ← ordinaryIndex_apply, hi, if_pos hj]
  have hblock : 1 ≤ ∑ i ∈ Finset.range s, c i := by
    have hle := Finset.single_le_sum (f := c) (s := Finset.range s)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.mod_lt i.val hs))
    rw [hc.map_mod_nat, hci] at hle
    exact hle
  change _ ≤ ∑ i ∈ Finset.range (2 * m + 1), b (i : ZMod (2 * m + 1))
  rw [heq]
  calc
    (2 * m + 1) / s ≤ ((2 * m + 1) / s) * ∑ i ∈ Finset.range s, c i :=
      Nat.le_mul_of_pos_right _ hblock
    _ = ∑ i ∈ Finset.range (2 * m + 1), c i := by
      rw [← sum_range_mul_of_periodic hc, Nat.mul_div_cancel' hsn]

end ReeF4.FixedSpaceEstimate
