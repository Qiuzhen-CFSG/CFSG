module

public import Stellmacher.SectionFiveToSeven.Defs

/-!
# A unique maximal 2-local subgroup over a Sylow subgroup

Let `S₀` be a nontrivial Sylow 2-subgroup of a finite group.  Its normalizer
is a 2-local subgroup containing `S₀`.  Finite maximality in the subgroup
lattice therefore supplies a maximal 2-local subgroup containing `S₀`; if
there are no two distinct such subgroups, that maximal member is unique.

This is the finite-lattice step implicit in the Section 11 reduction at
`refs/latex/stellmacher-n-group.tex`, lines 1975--1978.  The conclusion uses
the predicate consumed by alternative (c) of Stellmacher (5.1).
-/

namespace Stellmacher.SectionsFiveToSeven

universe u

/-- A nontrivial Sylow 2-subgroup lies in a unique maximal 2-local subgroup
when it does not lie in two distinct maximal 2-local subgroups. -/
public theorem exists_uniqueMaximalTwoLocalContaining_of_not_two
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (hS0 : (S0 : Subgroup H) ≠ ⊥)
    (hNoTwo : ¬ ∃ M₁ M₂ : Subgroup H,
      M₁ ≠ M₂ ∧
      IsMaximalTwoLocalContaining (S0 : Subgroup H) M₁ ∧
      IsMaximalTwoLocalContaining (S0 : Subgroup H) M₂) :
    ∃ M : Subgroup H,
      UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M := by
  let N : Subgroup H := Subgroup.normalizer (S0 : Set H)
  have hNLocal : IsTwoLocal N := by
    exact ⟨(S0 : Subgroup H), hS0, S0.isPGroup', rfl⟩
  obtain ⟨M, hNM, hMmax⟩ := Finite.exists_le_maximal hNLocal
  have hS0N : (S0 : Subgroup H) ≤ N := by
    exact Subgroup.le_normalizer
  have hMContaining :
      IsMaximalTwoLocalContaining (S0 : Subgroup H) M :=
    ⟨hMmax, hS0N.trans hNM⟩
  refine ⟨M, hMContaining, ?_⟩
  intro M' hM'
  by_contra hne
  exact hNoTwo ⟨M, M', (fun hEq => hne hEq.symm), hMContaining, hM'⟩

end Stellmacher.SectionsFiveToSeven
