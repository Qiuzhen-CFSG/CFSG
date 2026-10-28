module

public import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Tactic

/-!
# Binary labels of the symplectic tensor family

Separating the even and odd tensor positions gives the two restricted
highest-weight coordinates. A finite binary induction proves uniqueness;
the geometric-sum bound puts both coordinates in the source range [0, q-1].
This includes the empty subset and both extreme labels.

Source: GLS3, 2.8.1(a), 2.8.6(a), and 2.8.10(d),
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary.MarkedWeights

/-- The binary highest-weight label of parity `p`. -/
def label {n : ℕ} (S : Finset (Fin (2*n))) (p : ℕ) : ℕ :=
  ∑ j ∈ S.filter (fun j => j.val % 2 = p), 2 ^ (j.val / 2)

abbrev A {n : ℕ} (S : Finset (Fin (2*n))) : ℕ := label S 0
abbrev B {n : ℕ} (S : Finset (Fin (2*n))) : ℕ := label S 1

private def positions {n : ℕ} (S : Finset (Fin (2*n))) (p : ℕ) : Finset ℕ :=
  (S.filter (fun j => j.val % 2 = p)).image (fun j => j.val / 2)

private theorem label_positions {n : ℕ} (S : Finset (Fin (2*n))) (p : ℕ) :
    label S p = ∑ i ∈ positions S p, 2 ^ i := by
  rw [positions, Finset.sum_image]
  · rfl
  · intro i hi j hj h
    have hi := (Finset.mem_filter.mp hi).2
    have hj := (Finset.mem_filter.mp hj).2
    change i.val / 2 = j.val / 2 at h
    apply Fin.ext
    omega

theorem label_lt {n : ℕ} (S : Finset (Fin (2*n))) (p : ℕ) : label S p < 2^n := by
  rw [label_positions]
  apply Nat.geomSum_lt (by decide)
  intro i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
  have := j.isLt
  omega

theorem label_le_card_sub_one {n q : ℕ} (hq : q = 2^n)
    (S : Finset (Fin (2*n))) (p : ℕ) : 0 ≤ label S p ∧ label S p ≤ q-1 := by
  have := label_lt S p
  omega

theorem label_eq_zero_iff {n : ℕ} (S : Finset (Fin (2*n))) (p : ℕ) :
    label S p = 0 ↔ ∀ j ∈ S, j.val % 2 ≠ p := by
  simp only [label, Finset.sum_eq_zero_iff, Finset.mem_filter, and_imp]
  constructor
  · intro h j hj hp
    have hz := h j hj hp
    exact (Nat.ne_of_gt (pow_pos (by decide) _)) hz
  · intro h j hj hp
    exact (h j hj hp).elim

private theorem binary_sum_injective_bound (n : ℕ) (S T : Finset ℕ)
    (hS : ∀ i ∈ S, i < n) (hT : ∀ i ∈ T, i < n)
    (h : ∑ i ∈ S, 2^i = ∑ i ∈ T, 2^i) : S = T := by
  induction n generalizing S T with
  | zero =>
    have hs : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by intro i hi; exact Nat.not_lt_zero i (hS i hi))
    have ht : T = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by intro i hi; exact Nat.not_lt_zero i (hT i hi))
    exact hs.trans ht.symm
  | succ n ih =>
    have hs : ∀ i ∈ S.erase n, i < n := by
      intro i hi
      have hi' := Finset.mem_erase.mp hi
      have := hS i hi'.2
      omega
    have ht : ∀ i ∈ T.erase n, i < n := by
      intro i hi
      have hi' := Finset.mem_erase.mp hi
      have := hT i hi'.2
      omega
    have bs := Nat.geomSum_lt (by decide : 2 ≤ 2) hs
    have bt := Nat.geomSum_lt (by decide : 2 ≤ 2) ht
    have sum_erase (R : Finset ℕ) :
        ∑ i ∈ R, 2^i = (if n ∈ R then 2^n else 0) + ∑ i ∈ R.erase n, 2^i := by
      by_cases hn : n ∈ R
      · rw [if_pos hn, Finset.add_sum_erase _ _ hn]
      · simp [hn]
    rw [sum_erase S, sum_erase T] at h
    have hm : n ∈ S ↔ n ∈ T := by
      by_cases hnS : n ∈ S <;> by_cases hnT : n ∈ T <;> simp only [hnS, hnT, if_true, if_false] at h ⊢ <;> omega
    have he : ∑ i ∈ S.erase n, 2^i = ∑ i ∈ T.erase n, 2^i := by
      simp only [hm] at h
      exact Nat.add_left_cancel h
    have hi := ih _ _ hs ht he
    ext i
    by_cases hin : i = n
    · simpa [hin] using hm
    · simpa [Finset.mem_erase, hin] using Finset.ext_iff.mp hi i

theorem labels_injective {n : ℕ} :
    Function.Injective (fun S : Finset (Fin (2*n)) => (A S, B S)) := by
  intro S T h
  have hp (p : ℕ) (hp : p < 2) : positions S p = positions T p := by
    apply binary_sum_injective_bound n
    · intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      have := j.isLt
      omega
    · intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      have := j.isLt
      omega
    · rw [← label_positions, ← label_positions]
      have h0 := congrArg Prod.fst h
      have h1 := congrArg Prod.snd h
      rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl
      · exact h0
      · exact h1
  have hm (S T : Finset (Fin (2*n)))
      (hp : ∀ p < 2, positions S p = positions T p) (j : Fin (2*n))
      (hj : j ∈ S) : j ∈ T := by
    have hjp : j.val / 2 ∈ positions S (j.val % 2) :=
      Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, rfl⟩, rfl⟩
    rw [hp _ (Nat.mod_lt _ (by decide))] at hjp
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hjp
    have hk' := Finset.mem_filter.mp hk
    have : k = j := Fin.ext (by omega)
    simpa [this] using hk'.1
  exact Finset.Subset.antisymm (fun j => hm S T hp j)
    (fun j => hm T S (fun p h => (hp p h).symm) j)

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary.MarkedWeights
