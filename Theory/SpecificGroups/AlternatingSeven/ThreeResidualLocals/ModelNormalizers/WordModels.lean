module

public import Theory.SpecificGroups.AlternatingSeven.ThreeResidualLocals.Models
public import Theory.SpecificGroups.AlternatingSeven.ThreeResidualLocals.Generation
public import Theory.SpecificGroups.AlternatingSeven.ThreeResidualLocals.Partition
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.Tactic

/-!
# Twelve-element word models for the three A₄ actions

The finite action calculations are carried out in the literal permutation group
on `Fin 7`.  The generated A₄ groups are identified with checked twelve-element
word tables. The normalizer membership criterion reduces subsequent calculations
to the two generators. The remaining normalizer and residual calculations are
proved in the other modules of this directory, independently of the action
classification.

Source: Aschbacher–Smith 15.3.43, printed p.1140.
-/

@[expose] public section

open Subgroup Equiv
namespace AlternatingSeven.ThreeResidualLocals

local instance : Fintype (Equiv.Perm (Fin 7)) := fintypePerm

instance (g : Equiv.Perm (Fin 7)) : Decidable (g ∈ alternatingGroup (Fin 7)) :=
  inferInstanceAs (Decidable (g.sign = 1))

/-- The setwise stabilizer of the four-point block `{0,1,2,3}`. -/
def fourPointSet : Set (Fin 7) := {x | x.val < 4}

def fourPointSetwiseStabilizer : Subgroup (Equiv.Perm (Fin 7)) := {
  carrier := {g | ∀ x, x ∈ fourPointSet ↔ g x ∈ fourPointSet}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro a b ha hb x
    change x ∈ fourPointSet ↔ a (b x) ∈ fourPointSet
    exact (hb x).trans (ha (b x))
  inv_mem' := by
    intro a ha x
    simpa using (ha (a⁻¹ x)).symm
}

instance (g : Equiv.Perm (Fin 7)) : Decidable (g ∈ fourPointSetwiseStabilizer) :=
  inferInstanceAs (Decidable (∀ x, x.val < 4 ↔ (g x).val < 4))

def words12 (x y : Equiv.Perm (Fin 7)) : Fin 12 → Equiv.Perm (Fin 7) := ![
  1, x, y, x * x, x * y, y * x, x * x * y, x * y * x, y * x * x,
  y * x * y, x * x * y * x, x * y * x * x]

private theorem words12_mem (x y : Equiv.Perm (Fin 7))
    (hx : x ∈ Subgroup.closure ({x, y} : Set (Equiv.Perm (Fin 7))))
    (hy : y ∈ Subgroup.closure ({x, y} : Set (Equiv.Perm (Fin 7)))) :
    ∀ i, words12 x y i ∈ Subgroup.closure ({x, y} : Set (Equiv.Perm (Fin 7))) := by
  intro i
  fin_cases i <;> simp [words12]
  all_goals try exact hx
  all_goals try exact hy
  all_goals try exact (Subgroup.closure ({x, y} : Set _)).mul_mem hx hx
  all_goals try exact (Subgroup.closure ({x, y} : Set _)).mul_mem hx hy
  all_goals try exact (Subgroup.closure ({x, y} : Set _)).mul_mem hy hx
  all_goals try exact (Subgroup.closure ({x, y} : Set _)).mul_mem ((Subgroup.closure ({x, y} : Set _)).mul_mem hx hx) hy
  all_goals try exact (Subgroup.closure ({x, y} : Set _)).mul_mem ((Subgroup.closure ({x, y} : Set _)).mul_mem hx hy) hx
  all_goals try exact (Subgroup.closure ({x, y} : Set _)).mul_mem ((Subgroup.closure ({x, y} : Set _)).mul_mem hy hx) hx
  all_goals try exact (Subgroup.closure ({x, y} : Set _)).mul_mem ((Subgroup.closure ({x, y} : Set _)).mul_mem hy hx) hy
  all_goals try exact (Subgroup.closure ({x, y} : Set _)).mul_mem ((Subgroup.closure ({x, y} : Set _)).mul_mem ((Subgroup.closure ({x, y} : Set _)).mul_mem hx hx) hy) hx
  all_goals exact (Subgroup.closure ({x, y} : Set _)).mul_mem ((Subgroup.closure ({x, y} : Set _)).mul_mem ((Subgroup.closure ({x, y} : Set _)).mul_mem hx hy) hx) hx


def words12Subgroup (x y : Equiv.Perm (Fin 7))
    (hm : ∀ i j : Fin 12, ∃ k : Fin 12,
      words12 x y i * words12 x y j = words12 x y k)
    (hi : ∀ i : Fin 12, ∃ k : Fin 12,
      (words12 x y i)⁻¹ = words12 x y k) : Subgroup (Equiv.Perm (Fin 7)) := {
  carrier := Set.range (words12 x y)
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hm i j
    exact ⟨k, hk.symm⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := hi i
    exact ⟨k, hk.symm⟩
}

theorem natural_words_mul : ∀ i j : Fin 12, ∃ k : Fin 12,
    words12 naturalThree fourFlip i * words12 naturalThree fourFlip j =
      words12 naturalThree fourFlip k := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [words12] <;> decide +kernel

theorem natural_words_inv : ∀ i : Fin 12, ∃ k : Fin 12,
    (words12 naturalThree fourFlip i)⁻¹ = words12 naturalThree fourFlip k := by
  intro i
  fin_cases i <;> simp [words12] <;> decide +kernel

theorem diagonal_words_mul : ∀ i j : Fin 12, ∃ k : Fin 12,
    words12 diagonalThree fourFlip i * words12 diagonalThree fourFlip j =
      words12 diagonalThree fourFlip k := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [words12] <;> decide +kernel

theorem diagonal_words_inv : ∀ i : Fin 12, ∃ k : Fin 12,
    (words12 diagonalThree fourFlip i)⁻¹ = words12 diagonalThree fourFlip k := by
  intro i
  fin_cases i <;> simp [words12] <;> decide +kernel

theorem paired_words_mul : ∀ i j : Fin 12, ∃ k : Fin 12,
    words12 pairedThree fourFlip i * words12 pairedThree fourFlip j =
      words12 pairedThree fourFlip k := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [words12] <;> decide +kernel

theorem paired_words_inv : ∀ i : Fin 12, ∃ k : Fin 12,
    (words12 pairedThree fourFlip i)⁻¹ = words12 pairedThree fourFlip k := by
  intro i
  fin_cases i <;> simp [words12] <;> decide +kernel

def naturalExplicit : Subgroup (Equiv.Perm (Fin 7)) :=
  words12Subgroup naturalThree fourFlip natural_words_mul natural_words_inv

instance (g : Equiv.Perm (Fin 7)) : Decidable (g ∈ naturalExplicit) := by
  unfold naturalExplicit words12Subgroup
  change Decidable (∃ i : Fin 12, words12 naturalThree fourFlip i = g)
  infer_instance

theorem naturalFour_eq_explicit : naturalFour = naturalExplicit := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro g hg
    rcases hg with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro _ ⟨i, rfl⟩
    exact words12_mem naturalThree fourFlip
      (subset_closure (by simp))
      (subset_closure (by simp)) i

def diagonalExplicit : Subgroup (Equiv.Perm (Fin 7)) :=
  words12Subgroup diagonalThree fourFlip diagonal_words_mul diagonal_words_inv

def pairedExplicit : Subgroup (Equiv.Perm (Fin 7)) :=
  words12Subgroup pairedThree fourFlip paired_words_mul paired_words_inv

instance (g : Equiv.Perm (Fin 7)) : Decidable (g ∈ diagonalExplicit) := by
  unfold diagonalExplicit words12Subgroup
  change Decidable (∃ i : Fin 12, words12 diagonalThree fourFlip i = g)
  infer_instance
instance (g : Equiv.Perm (Fin 7)) : Decidable (g ∈ pairedExplicit) := by
  unfold pairedExplicit words12Subgroup
  change Decidable (∃ i : Fin 12, words12 pairedThree fourFlip i = g)
  infer_instance

theorem diagonalFour_eq_explicit : diagonalFour = diagonalExplicit := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro g hg
    rcases hg with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro _ ⟨i, rfl⟩
    apply words12_mem diagonalThree fourFlip
      (subset_closure (by simp))
      (subset_closure (by simp))

theorem pairedFour_eq_explicit : pairedFour = pairedExplicit := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro g hg
    rcases hg with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro _ ⟨i, rfl⟩
    apply words12_mem pairedThree fourFlip
      (subset_closure (by simp))
      (subset_closure (by simp))

/-- The literal natural model has twelve elements. -/
theorem naturalFour_card : Nat.card naturalFour = 12 := by
  rw [naturalFour_eq_explicit]
  change Nat.card (Set.range (words12 naturalThree fourFlip)) = 12
  rw [Nat.card_range_of_injective (by decide +kernel :
    Function.Injective (words12 naturalThree fourFlip))]
  simp

/-- The literal diagonal model has twelve elements. -/
theorem diagonalFour_card : Nat.card diagonalFour = 12 := by
  rw [diagonalFour_eq_explicit]
  change Nat.card (Set.range (words12 diagonalThree fourFlip)) = 12
  rw [Nat.card_range_of_injective (by decide +kernel :
    Function.Injective (words12 diagonalThree fourFlip))]
  simp

/-- The literal paired model has twelve elements. -/
theorem pairedFour_card : Nat.card pairedFour = 12 := by
  rw [pairedFour_eq_explicit]
  change Nat.card (Set.range (words12 pairedThree fourFlip)) = 12
  rw [Nat.card_range_of_injective (by decide +kernel :
    Function.Injective (words12 pairedThree fourFlip))]
  simp

/-- A finite two-generated subgroup is normalized precisely when both conjugated
 generators remain in the subgroup. -/
theorem mem_normalizer_pair_closure_iff (x y g : Perm7) :
    g ∈ normalizer (closure ({x, y} : Set Perm7) : Set Perm7) ↔
      g * x * g⁻¹ ∈ closure ({x, y} : Set Perm7) ∧
      g * y * g⁻¹ ∈ closure ({x, y} : Set Perm7) := by
  constructor
  · intro h
    exact ⟨(h x).mp (subset_closure (by simp)),
      (h y).mp (subset_closure (by simp))⟩
  · intro h
    apply mem_normalizer_fintype
    intro z hz
    have hmap : (closure ({x, y} : Set Perm7)).map (MulAut.conj g).toMonoidHom ≤
        closure ({x, y} : Set Perm7) := by
      rw [MonoidHom.map_closure, closure_le]
      rintro _ ⟨a, ha, rfl⟩
      rcases ha with rfl | rfl
      · exact h.1
      · exact h.2
    exact hmap (mem_map.mpr ⟨z, hz, rfl⟩)

end AlternatingSeven.ThreeResidualLocals
