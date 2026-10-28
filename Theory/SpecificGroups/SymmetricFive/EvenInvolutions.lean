module
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Fintype.Perm
/-!
# The fifteen even involutions of S₅

The five-letter table gives the fifteen nonidentity even involutions,
all with cycle type (2,2). Equality of cycle types gives their conjugacy
in the actual symmetric group. This supplies the quotient factor in
Aschbacher--Smith J.2.7(8), printed p.437.
-/

public section
namespace Equiv.Perm

private instance : DecidablePred (· ∈ alternatingGroup (Fin 5)) :=
  fun σ => decidable_of_iff (sign σ=1) mem_alternatingGroup.symm


/-- The even involutions in S₅ form a set of fifteen elements. -/
theorem even_involutions_five_card :
    Nat.card {σ : Equiv.Perm (Fin 5) // σ∈alternatingGroup (Fin 5) ∧ σ^2=1 ∧ σ≠1}=15 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- Every even nonidentity involution in S₅ has the double-transposition type. -/
theorem even_involution_five_cycleType (σ : Equiv.Perm (Fin 5))
    (he : σ∈alternatingGroup (Fin 5)) (hs : σ^2=1) (hn : σ≠1) : σ.cycleType={2,2} := by
  revert σ
  decide +kernel

/-- All fifteen even involutions are conjugate inside S₅. -/
theorem even_involutions_five_isConj (σ τ : Equiv.Perm (Fin 5))
    (hσ : σ∈alternatingGroup (Fin 5) ∧ σ^2=1 ∧ σ≠1)
    (hτ : τ∈alternatingGroup (Fin 5) ∧ τ^2=1 ∧ τ≠1) : IsConj σ τ :=
  isConj_of_cycleType_eq ((even_involution_five_cycleType σ hσ.1 hσ.2.1 hσ.2.2).trans
    (even_involution_five_cycleType τ hτ.1 hτ.2.1 hτ.2.2).symm)

end Equiv.Perm
