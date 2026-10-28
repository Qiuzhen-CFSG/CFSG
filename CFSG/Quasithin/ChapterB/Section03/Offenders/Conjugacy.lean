module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# Subgroup conjugacy transport for the offender families

Conjugate permutation subgroups have equal binary rank, and conjugation
preserves nontrivial elementary abelian two-subgroups. Unpacking the chosen
orientation of `IsConjugateTo` reduces both statements to the general
`Representation.BinaryOffender` conjugation lemmas.

These shared adapters support the degree-six and degree-eight families in
Aschbacher–Smith, *The Classification of Quasithin Groups*, Proposition B.3.2,
printed pp. 83–84; they do not assert the classification of those families.
-/

public section
namespace CFSG.Quasithin.ChapterB.Offenders
open Representation.BinaryOffender

variable {n : ℕ} {A B : Subgroup (Equiv.Perm (Fin n))}

/-- Conjugate subgroups have the same binary rank. -/
theorem IsConjugateTo.rank_eq (h : IsConjugateTo A B) : rank A = rank B := by
  obtain ⟨g, rfl⟩ := h
  exact rank_map_conj B g

/-- Elementary-two structure is invariant under subgroup conjugacy. -/
theorem IsConjugateTo.isElementaryTwo (h : IsConjugateTo A B)
    (hB : IsElementaryTwo B) : IsElementaryTwo A := by
  obtain ⟨g, rfl⟩ := h
  exact hB.map_conj g

end CFSG.Quasithin.ChapterB.Offenders
