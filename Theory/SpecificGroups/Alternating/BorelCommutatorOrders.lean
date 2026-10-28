module

public import Theory.SpecificGroups.AlternatingSix.SmallIndex
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Commutator orders detecting odd Borel actors

An odd permutation of four letters has a nonidentity cubic commutator
with an element of A₄. In contrast, commutators in an A₅ point stabilizer
have square one: transport the stabilizer to A₄ and use its Klein-four
derived subgroup. The small A₄ calculations are checked by kernel reduction.

These statements distinguish the two actions on the first local factor
in Aschbacher--Smith, completion of 12.3.1, printed p.812.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement

namespace Theory.SpecificGroups.Alternating

/-- Odd four-letter actors have a nontrivial cubic commutator in A₄. -/
theorem four_odd_cubic_witness (t : Equiv.Perm (Fin 4))
    (ht : t ∉ alternatingGroup (Fin 4)) :
    ∃ a : alternatingGroup (Fin 4), ⁅a.val,t⁆ ^ 3 = 1 ∧ ⁅a.val,t⁆ ≠ 1 := by
  have h : ∀ s : Equiv.Perm (Fin 4), s.sign ≠ 1 →
      ∃ a : alternatingGroup (Fin 4), ⁅a.val,s⁆ ^ 3 = 1 ∧ ⁅a.val,s⁆ ≠ 1 := by
    decide +kernel
  exact h t (fun he => ht (Equiv.Perm.mem_alternatingGroup.mpr he))

/-- Commutators in an even five-letter point stabilizer have square one. -/
theorem five_borel_commutator_sq (i : Fin 5)
    (a b : alternatingGroup (Fin 5)) (ha : a.val i = i) (hb : b.val i = i) :
    ⁅a,b⁆ ^ 2 = 1 := by
  let B := MulAction.stabilizer (alternatingGroup (Fin 5)) i
  let e := AlternatingSix.SmallIndex.pointEquiv (n := 4) i
  have h : ∀ x y : alternatingGroup (Fin 4), ⁅x,y⁆ ^ 2 = 1 := by decide +kernel
  have he : (⁅(⟨a,ha⟩ : B),(⟨b,hb⟩ : B)⁆)^2 = 1 := by
    apply e.injective
    rw [map_pow,map_commutatorElement,map_one]
    exact h _ _
  exact congrArg Subtype.val he

end Theory.SpecificGroups.Alternating
