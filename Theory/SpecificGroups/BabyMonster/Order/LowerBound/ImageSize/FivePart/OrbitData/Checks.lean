module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.FivePart.OrbitData.CheckPart0
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.FivePart.OrbitData.CheckPart1
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.FivePart.OrbitData.CheckPart2
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.FivePart.OrbitData.CheckPart3
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.FivePart.OrbitData.CheckPart4
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.FivePart.OrbitData.CheckPart5
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.FivePart.OrbitData.CheckPart6
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.FivePart.OrbitData.CheckPart7

/-!
# Assembling the finite five-part checks

All 245 blocks of at most 64 entries are checked separately by the kernel.
The resulting pointwise facts certify distinct signatures, inverse permutation
tables and the breadth-first spanning tree.
-/

@[expose] public section
namespace BabyMonster.OrderLowerBound.FivePart.OrbitTables

private theorem block_checks (b : Fin 245) : checkBlock b.val = true := by
  by_cases h0 : b.val < 32
  · have h := checkPart0 ⟨b.val - 0, by omega⟩
    simpa only [Nat.add_sub_of_le (by omega : 0 ≤ b.val)] using h
  by_cases h1 : b.val < 64
  · have h := checkPart1 ⟨b.val - 32, by omega⟩
    simpa only [Nat.add_sub_of_le (by omega : 32 ≤ b.val)] using h
  by_cases h2 : b.val < 96
  · have h := checkPart2 ⟨b.val - 64, by omega⟩
    simpa only [Nat.add_sub_of_le (by omega : 64 ≤ b.val)] using h
  by_cases h3 : b.val < 128
  · have h := checkPart3 ⟨b.val - 96, by omega⟩
    simpa only [Nat.add_sub_of_le (by omega : 96 ≤ b.val)] using h
  by_cases h4 : b.val < 160
  · have h := checkPart4 ⟨b.val - 128, by omega⟩
    simpa only [Nat.add_sub_of_le (by omega : 128 ≤ b.val)] using h
  by_cases h5 : b.val < 192
  · have h := checkPart5 ⟨b.val - 160, by omega⟩
    simpa only [Nat.add_sub_of_le (by omega : 160 ≤ b.val)] using h
  by_cases h6 : b.val < 224
  · have h := checkPart6 ⟨b.val - 192, by omega⟩
    simpa only [Nat.add_sub_of_le (by omega : 192 ≤ b.val)] using h
  have h := checkPart7 ⟨b.val - 224, by have := b.isLt; omega⟩
  simpa only [Nat.add_sub_of_le (by omega : 224 ≤ b.val)] using h

private theorem entry_checks (i : Fin 15625) : entryCheck i :=
  entryCheck_of_blocks block_checks i

theorem signature_injective : Function.Injective signature := by
  intro i j h
  apply Fin.ext
  rw [← (entry_checks i).1, ← (entry_checks j).1, h]

private theorem inverse_checks (i : Fin 15625) :
    backward 0 (forward 0 i) = i ∧ forward 0 (backward 0 i) = i ∧
    backward 1 (forward 1 i) = i ∧ forward 1 (backward 1 i) = i :=
  ⟨(entry_checks i).2.1, (entry_checks i).2.2.1,
    (entry_checks i).2.2.2.1, (entry_checks i).2.2.2.2.1⟩

def perm (j : Fin 2) : Equiv.Perm (Fin 15625) where
  toFun := forward j
  invFun := backward j
  left_inv := by
    intro i
    rcases Fin.eq_zero_or_eq_succ j with h | ⟨k, h⟩
    · simpa only [h] using (inverse_checks i).1
    · have hk : k = 0 := Fin.eq_zero k
      subst hk
      simpa only [h, Fin.succ_zero_eq_one] using (inverse_checks i).2.2.1
  right_inv := by
    intro i
    rcases Fin.eq_zero_or_eq_succ j with h | ⟨k, h⟩
    · simpa only [h] using (inverse_checks i).2.1
    · have hk : k = 0 := Fin.eq_zero k
      subst hk
      simpa only [h, Fin.succ_zero_eq_one] using (inverse_checks i).2.2.2


theorem parent_lt (i : Fin 15625) (hi : i ≠ 0) : (parent i).val < i.val :=
  ((entry_checks i).2.2.2.2.2 hi).1

theorem parent_edge (i : Fin 15625) (hi : i ≠ 0) : perm (edge i) (parent i) = i :=
  ((entry_checks i).2.2.2.2.2 hi).2

end BabyMonster.OrderLowerBound.FivePart.OrbitTables
