module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.PresentationBound.Core
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.PresentationBound.Certificate.Context

/-!
# Realization of the exceptional presentation's coset certificate

Every relator loop is one of the eleven literal defining words. The only
subgroup loop is the second generator, which belongs to its cyclic subgroup.
The remaining defining edges are realized by an acyclic tree in the abstract
presented group. No finite group model supplies an equation here.

Source purpose: the exceptional comparison in GLS3 §2.2 and its application
to Aschbacher–Smith I.1.4(1).
-/

public section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.PresentationBound

open Subgroup.CosetWordCertificate Certificate

theorem certificate_valid : Valid context cyclic generator (definitions.repr generator) := by
  apply definitions.valid
  · intro a ha
    have he : a = (1, true) := by simpa only [context, beq_iff_eq] using ha
    subst a
    simpa only [eval_letter, ite_true, cyclic] using Subgroup.mem_zpowers (generator 1)
  · intro r
    by_cases hr : r < 11
    · simpa only [relatorWords, dif_pos hr] using relator_eval ⟨r, hr⟩
    · simp [relatorWords, hr]

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.PresentationBound
