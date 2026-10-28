module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The derived subgroup of the binary two-dimensional linear group

Transport the derived subgroup along the checked GL₂(2) ≃ S₃ marking.
Its image is the alternating subgroup of order three. The six-element
commutator calculation is checked by the kernel.

This extends the marked Levi-model API. The original point-residual
chief-count application in Chapter14.OriginalSource.ChiefBound uses this
cardinality for the literal quotient L₁/O₂(L₁).

Source application: Aschbacher--Smith 14.7.10, printed p.1045.
-/

public section
open Subgroup
open scoped commutatorElement
namespace BinaryLinear.SmallParabolicLevi

/-- GL₂(2) has derived subgroup of order three under its actual S₃ marking. -/
theorem derived_two_card :
    Nat.card (commutator (BinaryLinear.OuterCyclic.LinearGroup 2)) = 3 := by
  have h3 : commutator (Equiv.Perm (Fin 3)) = alternatingGroup (Fin 3) := by
    apply le_antisymm
    · exact Abelianization.commutator_subset_ker Equiv.Perm.sign
    · intro g hg
      have h : ∀ g : Equiv.Perm (Fin 3), Equiv.Perm.sign g = 1 →
          ∃ a b : Equiv.Perm (Fin 3), ⁅a,b⁆ = g := by decide +kernel
      obtain ⟨a,b,rfl⟩ := h g hg
      exact commutator_mem_commutator (mem_top _) (mem_top _)
  let e := BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree
  have hm : (commutator (BinaryLinear.OuterCyclic.LinearGroup 2)).map e.toMonoidHom =
      alternatingGroup (Fin 3) := by
    rw [_root_.map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ e.surjective,
      ← _root_.commutator_def,h3]
  rw [← card_map_of_injective (K := commutator (BinaryLinear.OuterCyclic.LinearGroup 2))
    (f := e.toMonoidHom) e.injective,hm,nat_card_alternatingGroup,Nat.card_fin]
  rfl

end BinaryLinear.SmallParabolicLevi
