module

public import Theory.SpecificGroups.AlternatingSeven.DihedralLocals.CubicCatalogue
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Complement
public import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-!
# The fixed dihedral subgroup and proper stabilizers in A₇

The eight words r^i s^j form a Sylow subgroup of A₇. Each pair of the four
cubic representatives lies, together with these words, in an explicit proper
stabilizer: the four-point block, the seventh point, or one of two Fano planes.
The same even three-cycle escapes every stabilizer.

Source: the local inspection in Aschbacher--Smith F.6.18, printed p.310.
-/

@[expose] public section
open Equiv Subgroup
open scoped Pointwise
namespace AlternatingSeven.DihedralLocals

private theorem words_mul (i j : Fin 8) : ∃ k : Fin 8, tWord i * tWord j = tWord k := by
  decide +revert +kernel
private theorem words_inv (i : Fin 8) : ∃ j : Fin 8, (tWord i)⁻¹ = tWord j := by
  decide +revert +kernel

/-- The actual eight-element permutation subgroup, with computable normal forms. -/
def twoGroup : Subgroup Perm7 where
  carrier := Set.range tWord
  one_mem' := ⟨0, by decide⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := words_mul i j
    exact ⟨k, hk.symm⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := words_inv i
    exact ⟨j, hj.symm⟩

theorem r_mem_twoGroup : r ∈ twoGroup := ⟨1, by decide⟩
theorem s_mem_twoGroup : s ∈ twoGroup := ⟨4, by decide⟩
theorem tWord_mem_twoGroup (i : Fin 8) : tWord i ∈ twoGroup := ⟨i, rfl⟩
theorem r_four : r ^ 4 = 1 := by decide
theorem r_square_ne : r ^ 2 ≠ 1 := by decide

theorem twoGroup_card : Nat.card twoGroup = 8 := by
  let f : Fin 8 → twoGroup := fun i => ⟨tWord i, tWord_mem_twoGroup i⟩
  have hi : Function.Injective tWord := by decide +kernel
  have hb : Function.Bijective f := ⟨fun i j h => hi (congrArg Subtype.val h), by
    rintro ⟨g, i, rfl⟩
    exact ⟨i, rfl⟩⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hb)]
  simp

theorem twoGroup_le_alternating : twoGroup ≤ alternatingGroup (Fin 7) := by
  rintro _ ⟨i, rfl⟩
  exact (by decide +kernel : ∀ i, Perm.sign (tWord i) = 1) i

/-- The fixed subgroup in the original alternating carrier. -/
def fixedTwoGroup : Subgroup A7 := twoGroup.subgroupOf (alternatingGroup (Fin 7))

theorem fixedTwoGroup_card : Nat.card fixedTwoGroup = 8 :=
  (Nat.card_congr (subgroupOfEquivOfLe twoGroup_le_alternating).toEquiv).trans twoGroup_card

/-- The explicit eight-group is Sylow in the actual A₇ carrier. -/
def fixedSylow : Sylow 2 A7 :=
  (IsPGroup.of_card (p := 2) (n := 3) fixedTwoGroup_card).toSylow (by
    have hc := fixedTwoGroup.card_mul_index
    have hA : Nat.card A7 = 2520 := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [fixedTwoGroup_card, hA] at hc
    have hi : fixedTwoGroup.index = 315 := by omega
    rw [hi]
    decide)

def block : Finset (Fin 7) := {0,1,2,3}
def planePlus : Finset (Finset (Fin 7)) :=
  {{0,1,5},{0,2,6},{0,3,4},{1,2,4},{1,3,6},{2,3,5},{4,5,6}}
def planeMinus : Finset (Finset (Fin 7)) :=
  {{0,1,4},{0,2,6},{0,3,5},{1,2,5},{1,3,6},{2,3,4},{4,5,6}}

/-- A proper overgroup for each pair of local cubic representatives. -/
def obstruction (i j : Fin 4) : Subgroup Perm7 :=
  if i ≠ 3 ∧ j ≠ 3 then MulAction.stabilizer Perm7 block else
  if i = 1 ∨ j = 1 then MulAction.stabilizer Perm7 planePlus else
  if i = 2 ∨ j = 2 then MulAction.stabilizer Perm7 planeMinus else
  MulAction.stabilizer Perm7 (6 : Fin 7)

private instance obstructionDecidable (i j : Fin 4) (g : Perm7) :
    Decidable (g ∈ obstruction i j) := by
  unfold obstruction
  split
  · change Decidable (g • block = block)
    infer_instance
  · split
    · change Decidable (g • planePlus = planePlus)
      infer_instance
    · split
      · change Decidable (g • planeMinus = planeMinus)
        infer_instance
      · change Decidable (g (6 : Fin 7) = 6)
        infer_instance

private def escaping : Perm7 := swap 0 1 * swap 1 6

private theorem obstruction_generators (i j : Fin 4) :
    r ∈ obstruction i j ∧ s ∈ obstruction i j ∧
      cubic i ∈ obstruction i j ∧ cubic j ∈ obstruction i j := by
  decide +revert +kernel

theorem twoGroup_le_obstruction (i j : Fin 4) : twoGroup ≤ obstruction i j := by
  rintro _ ⟨k, rfl⟩
  exact (obstruction i j).mul_mem
    ((obstruction i j).pow_mem (obstruction_generators i j).1 _)
    ((obstruction i j).pow_mem (obstruction_generators i j).2.1 _)

theorem cubic_mem_obstruction_left (i j : Fin 4) : cubic i ∈ obstruction i j :=
  (obstruction_generators i j).2.2.1

theorem cubic_mem_obstruction_right (i j : Fin 4) : cubic j ∈ obstruction i j :=
  (obstruction_generators i j).2.2.2

private theorem escaping_block : escaping • block ≠ block := by decide +kernel
private theorem escaping_plus : escaping • planePlus ≠ planePlus := by decide +kernel
private theorem escaping_minus : escaping • planeMinus ≠ planeMinus := by decide +kernel
private theorem escaping_point : escaping (6 : Fin 7) ≠ 6 := by decide

private theorem escaping_not_mem (i j : Fin 4) : escaping ∉ obstruction i j := by
  unfold obstruction
  split
  · exact escaping_block
  · split
    · exact escaping_plus
    · split
      · exact escaping_minus
      · exact escaping_point

private theorem escaping_even : escaping ∈ alternatingGroup (Fin 7) := by
  change Perm.sign escaping = 1
  decide

theorem alternating_not_le_obstruction (i j : Fin 4) :
    ¬ alternatingGroup (Fin 7) ≤ obstruction i j := by
  intro h
  exact escaping_not_mem i j (h escaping_even)

end AlternatingSeven.DihedralLocals
