module
public import Theory.GroupTheory.DihedralCyclicDerived
public import Theory.SpecificGroups.SymmetricEight.CentralPair
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# The noncyclic derived subgroup of an A₈ Sylow group

Two commutators of the standard even binary-tree generators are distinct
involutions. A cyclic group has a unique involution, so the derived subgroup
is noncyclic. The certificates are just equalities of eight-letter permutations;
Sylow conjugacy gives the result for every Sylow two-subgroup.

Source application: excluding the odd containing rows of Aschbacher–Smith
A.3.12 in the original A₈ section of 15.3.32(3), pp.47–48 and 1133.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory Equiv.Perm
open scoped commutatorElement
namespace AlternatingEight
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open Theory.SpecificGroups.SymmetricEight.CentralPair
private def a : evenTreeSylow :=
  ⟨⟨treeGenerator 0 * treeGenerator 1, mem_alternatingGroup.mpr (by decide +kernel)⟩, by
    change (⟨_, _⟩ : A8) ∈ (evenTreeSylow : Subgroup A8)
    rw [evenTreeSylow_coe]
    exact treeGroup.mul_mem (treeGenerator_mem 0) (treeGenerator_mem 1)⟩
private def b : evenTreeSylow :=
  ⟨⟨treeGenerator 4, mem_alternatingGroup.mpr (by decide +kernel)⟩, by
    change (⟨_, _⟩ : A8) ∈ (evenTreeSylow : Subgroup A8)
    rw [evenTreeSylow_coe]
    exact treeGenerator_mem 4⟩
private def c : evenTreeSylow :=
  ⟨⟨treeGenerator 6, mem_alternatingGroup.mpr (by decide +kernel)⟩, by
    change (⟨_, _⟩ : A8) ∈ (evenTreeSylow : Subgroup A8)
    rw [evenTreeSylow_coe]
    exact treeGenerator_mem 6⟩
private def f : evenTreeSylow →* S8 := A8.subtype.comp (evenTreeSylow : Subgroup A8).subtype
private theorem hf : Function.Injective f :=
  A8.subtype_injective.comp (evenTreeSylow : Subgroup A8).subtype_injective

theorem evenTreeSylow_derived_not_cyclic : ¬ IsCyclic (commutator evenTreeSylow) := by
  intro hcyc
  let := hcyc
  let x : commutator evenTreeSylow := ⟨⁅a,c⁆, commutator_mem_commutator (mem_top _) (mem_top _)⟩
  let y : commutator evenTreeSylow := ⟨⁅b,c⁆, commutator_mem_commutator (mem_top _) (mem_top _)⟩
  have hx : orderOf x = 2 := by
    rw [← orderOf_coe, ← orderOf_injective f hf]
    change orderOf (⁅treeGenerator 0 * treeGenerator 1, treeGenerator 6⁆) = 2
    apply orderOf_eq_prime <;> decide +kernel
  have hy : orderOf y = 2 := by
    rw [← orderOf_coe, ← orderOf_injective f hf]
    change orderOf (⁅treeGenerator 4, treeGenerator 6⁆) = 2
    apply orderOf_eq_prime <;> decide +kernel
  have hne : f x.val ≠ f y.val := by
    change ⁅treeGenerator 0 * treeGenerator 1, treeGenerator 6⁆ ≠
      ⁅treeGenerator 4, treeGenerator 6⁆
    decide +kernel
  exact hne (congrArg (fun v : commutator evenTreeSylow => f v.val)
    (IsCyclic.eq_of_orderOf_eq_two hx hy))
/-- Every Sylow two-subgroup of A₈ has noncyclic derived subgroup. -/
theorem sylow_derived_not_cyclic (S : Sylow 2 A8) : ¬ IsCyclic (commutator S) := by
  intro hS
  exact evenTreeSylow_derived_not_cyclic
    (derived_cyclic_of_injective (evenTreeSylow.equiv S).toMonoidHom
      (evenTreeSylow.equiv S).injective hS)

/-- Every A₈ Sylow two-subgroup contains two noncommuting involutions. -/
theorem exists_noncommuting_sylow_involutions (S : Sylow 2 A8) :
    ∃ x y : S, x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ x * y ≠ y * x := by
  have hb : b ^ 2 = 1 := by
    apply hf
    change (treeGenerator 4) ^ 2 = 1
    decide +kernel
  have hc : c ^ 2 = 1 := by
    apply hf
    change (treeGenerator 6) ^ 2 = 1
    decide +kernel
  have hbc : b * c ≠ c * b := by
    intro h
    have hh := congrArg f h
    change treeGenerator 4 * treeGenerator 6 = treeGenerator 6 * treeGenerator 4 at hh
    exact (by decide +kernel : treeGenerator 4 * treeGenerator 6 ≠
      treeGenerator 6 * treeGenerator 4) hh
  let e := evenTreeSylow.equiv S
  refine ⟨e b, e c, ?_, ?_, ?_⟩
  · rw [← map_pow, hb, map_one]
  · rw [← map_pow, hc, map_one]
  · intro h
    exact hbc (e.injective (by simpa only [map_mul] using h))

end AlternatingEight
