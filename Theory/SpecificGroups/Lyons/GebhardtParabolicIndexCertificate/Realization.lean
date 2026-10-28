module

public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.Relators
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.Context

/-!
# The parabolic certificate is realized by the actual subgroup tower

Only `a` and `b` provide initial subgroup loops. The representative tree supplies
its own defining equalities, and the nine relators hold by their literal
identification with Gebhardt's relations. Thus the checker proves equations
inside the parabolic, independently of any permutation realization.

Source: Gebhardt (2000), Section 3B.
-/

public section
namespace Lyons.Gebhardt.ParabolicIndexCertificate
open Subgroup.CosetWordCertificate LocalTower

theorem allowed_ok (a : Letter (Fin 3)) (ha : context.allowed a = true) :
    eval localGenerator [a] ∈ base.subgroupOf parabolic := by
  have h : a = (0, true) ∨ a = (1, true) := by
    simpa only [context, decide_eq_true_eq] using ha
  rcases h with rfl | rfl
  · exact generator_mem 2 0 (by decide)
  · exact generator_mem 2 1 (by decide)

theorem valid : Valid context (base.subgroupOf parabolic) localGenerator
    (definitions.repr localGenerator) :=
  definitions.valid relatorWords context.allowed allowed_ok relator_ok

end Lyons.Gebhardt.ParabolicIndexCertificate
