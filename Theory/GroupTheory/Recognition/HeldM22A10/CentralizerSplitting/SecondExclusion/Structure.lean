module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Enumeration
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Distinguished subgroups of the second nonsplit candidate

The central involution and the exceptional subgroup are specified as actual
permutations in the checked enumeration. The exceptional subgroup is the
centralizer of the involution in row 1; it has order 64. We also fix two
explicit generated subgroups for the remaining Sylow and character calculations.
Their Sylow and index properties are separate proof obligations.

The central involution is identified intrinsically by showing that every
central element is either it or the identity. Source problem:
Huppert--Blackburn III, XII.1.18(b), p.314.
-/

namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.Model
open NonsplitModels Subgroup

set_option maxRecDepth 100000

/-- A computable finite enumeration of the unchanged permutation carrier. -/
public instance instFintypeSecond : Fintype Second :=
  Fintype.ofBijective element (by exact element_bijective)

/-- The central involution in the second model. -/
@[expose] public def centralPoint : Second := element 117

/-- The involution whose centralizer supplies the exceptional subgroup. -/
@[expose] public def exceptionalPoint : Second := element 1

public theorem centralPoint_ne_one : centralPoint ≠ 1 := by decide +kernel

public theorem centralPoint_order : orderOf centralPoint = 2 :=
  orderOf_eq_prime (by decide +kernel) centralPoint_ne_one

private theorem centralPoint_commutes : ∀ i : Fin 384,
    centralPoint * element i = element i * centralPoint := by decide +kernel

public theorem centralPoint_mem_center : centralPoint ∈ center Second := by
  apply mem_center_iff.mpr
  intro x
  obtain ⟨i, rfl⟩ := element_bijective.2 x
  exact (centralPoint_commutes i).symm

private theorem center_rows : ∀ i : Fin 384,
    perm i * secondA = secondA * perm i →
    perm i * secondB = secondB * perm i → i = 0 ∨ i = 117 := by
  decide +kernel

public theorem center_cases (x : Second) (hx : x ∈ center Second) :
    x = 1 ∨ x = centralPoint := by
  obtain ⟨i, rfl⟩ := element_bijective.2 x
  have ha : secondA ∈ secondSubgroup := subset_closure (by simp)
  have hb : secondB ∈ secondSubgroup := subset_closure (by simp)
  have hc := mem_center_iff.mp hx
  have hi := center_rows i
    (congrArg Subtype.val (hc ⟨secondA, ha⟩).symm)
    (congrArg Subtype.val (hc ⟨secondB, hb⟩).symm)
  rcases hi with rfl | rfl
  · left
    decide +kernel
  · exact Or.inr rfl

public theorem exceptionalPoint_order : orderOf exceptionalPoint = 2 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

/-- An intrinsic subgroup of the actual second model, not a group-family tag. -/
@[expose] public def exceptionalSubgroup : Subgroup Second :=
  centralizer ({exceptionalPoint} : Set Second)

public instance instDecidableMemExceptional : DecidablePred (· ∈ exceptionalSubgroup) := fun x =>
  decidable_of_iff (x * exceptionalPoint = exceptionalPoint * x)
    mem_centralizer_singleton_iff.symm

public theorem exceptionalSubgroup_card : Nat.card exceptionalSubgroup = 64 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- Concrete generators of the Sylow candidate used in the remaining calculation. -/
@[expose] public def sylowGenerators : Fin 7 → Second :=
  fun i => element (![33, 21, 9, 8, 83, 252, 117] i)

@[expose] public def sylowSubgroup : Subgroup Second :=
  closure (Set.range sylowGenerators)

/-- Concrete generators of the proposed transfer kernel. -/
@[expose] public def transferGenerators : Fin 6 → Second :=
  fun i => element (![33, 83, 109, 53, 1, 117] i)

@[expose] public def transferSubgroup : Subgroup Second :=
  closure (Set.range transferGenerators)

end Theory.GroupTheory.HeldM22A10.SecondExclusion.Model
