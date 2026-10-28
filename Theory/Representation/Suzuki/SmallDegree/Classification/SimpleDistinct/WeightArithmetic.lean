module

public import Theory.Representation.Suzuki.SmallDegree.Classification.SimpleDistinct.HighestVector

/-!
# Recovering Suzuki supports from highest-line characters

The binary sum of a subset of `Fin (2*m+1)` determines that subset. The torus
weight multiplier `1+2^m` is coprime to `2^(2*m+1)-1`, so equal highest-line
characters determine the binary sums modulo the torus order. Equal support
cardinalities separate the sole boundary collision, empty versus full support.

This supplies the arithmetic step in distinctness for the literal tensors,
without a simplicity or classification assumption. Sources: GLS3, 2.8.6(b)
(with the corrected `2*m+1` factors); Guralnick--Malle, *Classification of
2F-modules, II*, §3.1, equation (3.2).
-/

public noncomputable section

namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural

private theorem sum_binary_range (n : ℕ) :
    (∑ i ∈ Finset.range n, 2 ^ i) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega

private theorem sum_binary_lt (n : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range n) :
    ∑ i ∈ S, 2 ^ i < 2 ^ n := by
  have := Finset.sum_le_sum_of_subset hS (f := fun i => 2 ^ i)
  have := sum_binary_range n
  omega

private theorem binary_sum_injective (n : ℕ) (S T : Finset ℕ)
    (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n)
    (he : ∑ i ∈ S, 2 ^ i = ∑ i ∈ T, 2 ^ i) : S = T := by
  induction n generalizing S T with
  | zero =>
    have hs : S = ∅ := Finset.subset_empty.mp (by simpa using hS)
    have ht : T = ∅ := Finset.subset_empty.mp (by simpa using hT)
    rw [hs, ht]
  | succ n ih =>
    have hS' : S.erase n ⊆ Finset.range n := by
      intro i hi
      have h := hS (Finset.mem_of_mem_erase hi)
      have hn := (Finset.mem_erase.mp hi).1
      simp only [Finset.mem_range] at h ⊢
      omega
    have hT' : T.erase n ⊆ Finset.range n := by
      intro i hi
      have h := hT (Finset.mem_of_mem_erase hi)
      have hn := (Finset.mem_erase.mp hi).1
      simp only [Finset.mem_range] at h ⊢
      omega
    have hSl := sum_binary_lt n (S.erase n) hS'
    have hTl := sum_binary_lt n (T.erase n) hT'
    by_cases hs : n ∈ S <;> by_cases ht : n ∈ T
    · have hes := Finset.sum_erase_add S (fun i => 2 ^ i) hs
      have het := Finset.sum_erase_add T (fun i => 2 ^ i) ht
      have he' := ih (S.erase n) (T.erase n) hS' hT' (by omega)
      calc S = insert n (S.erase n) := (Finset.insert_erase hs).symm
           _ = insert n (T.erase n) := by rw [he']
           _ = T := Finset.insert_erase ht
    · have hes := Finset.sum_erase_add S (fun i => 2 ^ i) hs
      rw [Finset.erase_eq_of_notMem ht] at hTl
      omega
    · have het := Finset.sum_erase_add T (fun i => 2 ^ i) ht
      rw [Finset.erase_eq_of_notMem hs] at hSl
      omega
    · rw [Finset.erase_eq_of_notMem hs] at hS'
      rw [Finset.erase_eq_of_notMem ht] at hT'
      exact ih S T hS' hT' he

theorem supportWeight_lt (m : ℕ) (I : Support m) : supportWeight I < 2 ^ (2 * m + 1) := by
  have hb : I.map Fin.valEmbedding ⊆ Finset.range (2 * m + 1) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    exact Finset.mem_range.mpr j.isLt
  simpa [Finset.sum_map, supportWeight] using sum_binary_lt (2 * m + 1) _ hb

theorem supportWeight_injective (m : ℕ) : Function.Injective (@supportWeight m) := by
  intro I J he
  apply Finset.map_injective Fin.valEmbedding
  apply binary_sum_injective (2 * m + 1)
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    exact Finset.mem_range.mpr j.isLt
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    exact Finset.mem_range.mpr j.isLt
  · simpa [Finset.sum_map, supportWeight] using he

@[simp] theorem supportWeight_eq_zero_iff (m : ℕ) (I : Support m) :
    supportWeight I = 0 ↔ I = ∅ := by
  constructor
  · intro h
    exact supportWeight_injective m (show supportWeight I = supportWeight ∅ by
      simpa [supportWeight] using h)
  · rintro rfl
    simp [supportWeight]

theorem highestWeight_coprime (m : ℕ) : (1 + 2 ^ m).Coprime (2 ^ (2 * m + 1) - 1) := by
  have hp : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
  have he : 2 ^ (2 * m + 1) = 2 * (2 ^ m) ^ 2 := by
    rw [pow_add, pow_one, Nat.mul_comm 2 m, pow_mul]
    ring
  have he' : 2 ^ (2 * m + 1) - 1 = 1 + (2 * (2 ^ m - 1)) * (1 + 2 ^ m) := by
    rw [he]
    have he'' : 2 * (2 ^ m) ^ 2 = (1 + (2 * (2 ^ m - 1)) * (1 + 2 ^ m)) + 1 := by
      nlinarith [Nat.sub_add_cancel hp]
    omega
  rw [he', Nat.coprime_add_mul_right_right]
  exact Nat.coprime_one_right _


/-- Equal characters and equal dimensions recover every support, including the
empty/full residue collision. -/
theorem support_eq_of_weight_characters (m : ℕ) {I J : Support m}
    (hcard : I.card = J.card)
    (hchar : ∀ t : (F m)ˣ, t.val ^ ((1 + 2 ^ m) * supportWeight I) =
      t.val ^ ((1 + 2 ^ m) * supportWeight J)) : I = J := by
  by_cases hI : I = ∅
  · have hJ : J = ∅ := Finset.card_eq_zero.mp (by simpa [hI] using hcard.symm)
    rw [hI, hJ]
  have hJ : J ≠ ∅ := by
    intro h
    apply hI
    exact Finset.card_eq_zero.mp (by simpa [h] using hcard)
  have hi0 : supportWeight I ≠ 0 := by simpa using hI
  have hj0 : supportWeight J ≠ 0 := by simpa using hJ
  have hi := supportWeight_lt m I
  have hj := supportWeight_lt m J
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := (F m)ˣ)
  have ho : orderOf t = 2 ^ (2 * m + 1) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ht, Nat.card_units]
    rw [GaloisField.card 2 (2 * m + 1) (by omega)]
  have ho' : orderOf (t ^ (1 + 2 ^ m)) = 2 ^ (2 * m + 1) - 1 := by
    rw [orderOf_pow' t (by positivity), ho, (highestWeight_coprime m).symm.gcd_eq_one,
      Nat.div_one]
  have he : (t ^ (1 + 2 ^ m)) ^ supportWeight I =
      (t ^ (1 + 2 ^ m)) ^ supportWeight J := by
    apply Units.ext
    simpa only [← pow_mul, Units.val_pow_eq_pow_val] using hchar t
  have he' : (t ^ (1 + 2 ^ m)) ^ (supportWeight I - 1) =
      (t ^ (1 + 2 ^ m)) ^ (supportWeight J - 1) := by
    apply mul_right_cancel (b := t ^ (1 + 2 ^ m))
    simpa only [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ supportWeight I),
      Nat.sub_add_cancel (by omega : 1 ≤ supportWeight J)] using he
  have hh := pow_injOn_Iio_orderOf (x := t ^ (1 + 2 ^ m))
    (show supportWeight I - 1 < orderOf (t ^ (1 + 2 ^ m)) by rw [ho']; omega)
    (show supportWeight J - 1 < orderOf (t ^ (1 + 2 ^ m)) by rw [ho']; omega) he'
  exact supportWeight_injective m (by omega)
end Representation.SuzukiSmallDegree
