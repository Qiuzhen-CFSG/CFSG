module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.AlternatingSeven.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Tactic.Group

/-!
# Aligning a cycle-type action with the standard partition

Two permutations with cycle type `2³` are conjugate in S₇. Relabeling the
actual alternating central quotient by that conjugator makes the action
literal conjugation by `(01)(23)(45)`. The automorphism of the covering group
and the quotient kernel are unchanged by this choice of coordinates.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
1.1.5(3)(d) and the partition in 2.3.9(7)(c), printed pp.501 and 525–526.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.AlternatingSeven

open Equiv Subgroup

/-- Cycle types omit fixed points; the remaining seventh letter is fixed. -/
theorem tripleSwap_cycleType : tripleSwap.cycleType = {2, 2, 2} := by decide

variable {K : Type*} [Group K]

/-- Relabel the quotient to the standard partition without changing its kernel
or replacing the action on the covering group. -/
theorem exists_standard_coordinates (e : (K ⧸ center K) ≃* A7)
    (α : MulAut K) (σ : S7) (hσ : σ.cycleType = {2, 2, 2})
    (ha : ∀ x : K, (quotientMap e (α x) : S7) =
      σ * (quotientMap e x : S7) * σ⁻¹) :
    ∃ e' : (K ⧸ center K) ≃* A7, ActsAsTripleSwap e' α := by
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (Perm.isConj_iff_cycleType_eq.mpr (hσ.trans tripleSwap_cycleType.symm))
  let e' : (K ⧸ center K) ≃* A7 := e.trans (MulAut.conjNormal g)
  refine ⟨e', ?_⟩
  intro x
  change g * (quotientMap e (α x) : S7) * g⁻¹ =
    tripleSwap * (g * (quotientMap e x : S7) * g⁻¹) * tripleSwap⁻¹
  rw [ha, ← hg]
  group

end CFSG.Quasithin.Chapter2.ComponentRefinement.AlternatingSeven
end
