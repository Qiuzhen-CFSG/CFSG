module
public import Theory.SpecificGroups.GL2.DeterminantTwoPower
public import Theory.FieldTheory.RootsOfUnityCard
public import Mathlib.GroupTheory.Index

/-!
# Exact indices in the determinant two-power filtration

For a finite field F, if 2^n divides |F|-1 and m≤n, the actual determinant
level m has relative index 2^(n-m) in level n. In particular the zero level
has index 2^m in level m, and consecutive valid levels have index two.

The determinant map is surjective. Its kernel is the zero level, and the
image of level m is the actual group of 2^m-th roots of unity, whose
cardinality is 2^m under the divisor hypothesis. Multiplicativity of subgroup
relative indices gives the general formula.

These are the filtration indices stated before Alperin--Brauer--Gorenstein
II.2 Lemma 1 (article page 17), used for the matrix extension comparison in
II.3 Proposition 3. The result concerns the determinant-defined subgroups,
without assuming the desired abstract group recognition.
-/

namespace Matrix.GeneralLinearGroup

public theorem determinantTwoPower_zero_relIndex
    (F : Type*) [Field F] [Finite F] (m : ℕ)
    (hd : 2 ^ m ∣ Nat.card F - 1) :
    (determinantTwoPower F 0).relIndex (determinantTwoPower F m) = 2 ^ m := by
  rw [determinantTwoPower_zero, Subgroup.relIndex_ker]
  change Nat.card (((rootsOfUnity (2 ^ m) F).comap
    (det : GL (Fin 2) F →* Fˣ)).map det) = 2 ^ m
  rw [Subgroup.map_comap_eq_self_of_surjective (det_surjective (n := Fin 2))]
  exact FiniteField.card_rootsOfUnity_of_dvd F (2 ^ m) hd

public theorem determinantTwoPower_relIndex
    (F : Type*) [Field F] [Finite F] {m n : ℕ} (hmn : m ≤ n)
    (hd : 2 ^ n ∣ Nat.card F - 1) :
    (determinantTwoPower F m).relIndex (determinantTwoPower F n) = 2 ^ (n - m) := by
  have hdm : 2 ^ m ∣ Nat.card F - 1 := (pow_dvd_pow 2 hmn).trans hd
  have hi := Subgroup.relIndex_mul_relIndex
    (determinantTwoPower F 0) (determinantTwoPower F m) (determinantTwoPower F n)
    (determinantTwoPower_mono (Nat.zero_le m)) (determinantTwoPower_mono hmn)
  rw [determinantTwoPower_zero_relIndex F m hdm,
    determinantTwoPower_zero_relIndex F n hd] at hi
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < 2) m)
  rw [hi, ← pow_add, Nat.add_sub_of_le hmn]

public theorem determinantTwoPower_successor_relIndex
    (F : Type*) [Field F] [Finite F] (m : ℕ)
    (hd : 2 ^ (m + 1) ∣ Nat.card F - 1) :
    (determinantTwoPower F m).relIndex (determinantTwoPower F (m + 1)) = 2 := by
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel_left, pow_one] using
    determinantTwoPower_relIndex F (Nat.le_succ m) hd

end Matrix.GeneralLinearGroup
