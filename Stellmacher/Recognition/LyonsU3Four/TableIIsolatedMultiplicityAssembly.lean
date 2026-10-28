module
public import Stellmacher.Recognition.LyonsU3Four.TableIIsolatedRowSupport

/-!
# Exact isolated-branch catalogue multiplicities

Four explicit multiplicity vectors describe cases F and G and their column
reflections. The finite identities below compare all 89 candidate multiplicities
with the actual catalogue, including duplicate rows. They do not assert that
these vectors exhaust the Gram equations; that is a separate enumeration step.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), Table I and
Case 3, pp. 377–378.
-/
@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four.TableIIsolatedRows

/-- `false` selects F, `true` selects G. -/
def solutionCase : Bool → TableICase
  | false => .F
  | true => .G

def solutionVariant (c : Bool) : (solutionCase c).Variant := by
  cases c <;> exact ()

/-- The reflected orientation moves the exceptional orbit from 65–68 to 73–76. -/
def solution (c reflected : Bool) (a : Fin 89) : ℕ :=
  if a = 3 then 1
  else if a = 7 then (if c then 0 else 2)
  else if a = 8 then (if c then 3 else 2)
  else if a = 9 then (if c then 0 else 2)
  else if a = 10 then (if c then 1 else 0)
  else if 17 ≤ a.val ∧ a.val < 21 then 1
  else if reflected then (if 73 ≤ a.val ∧ a.val < 77 then 1 else 0)
  else if 65 ≤ a.val ∧ a.val < 69 then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Exact counts for the canonical orientation. -/
theorem solution_counts (c : Bool) : ∀ a,
    solution c false a = Fintype.card
      {j // tableIMatrix (solutionCase c) (solutionVariant c) j = row a} := by
  cases c <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- All rows of F and G are in the isolated support. -/
theorem solution_covered (c : Bool) : ∀ j, ∃ a,
    tableIMatrix (solutionCase c) (solutionVariant c) j = row a := by
  cases c <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Reflection interchanges the two orientations, preserving every multiplicity. -/
theorem solution_reflection (c : Bool) : ∀ a,
    solution c true (reflection a) = solution c false a := by
  cases c <;> decide

end Stellmacher.Recognition.LyonsU3Four.TableIIsolatedRows

namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
open TableIIsolatedRows
variable {I : Type*} [Fintype I] (d : GeneralizedDecompositionData I)

/-- Reflection acts on the finite support multiplicities by the explicit permutation. -/
theorem isolated_multiplicity_reflection (a : Fin 89) :
    d.reflectColumns.tableIRowMultiplicity (row a) =
      d.tableIRowMultiplicity (row (reflection a)) := by
  classical
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro j
  rw [d.isolated_normalized_reflection, row_reflection]
  constructor
  · intro hj
    have hh := congrArg reflect hj
    simpa using hh
  · intro hj
    rw [hj, reflect_twice]

private theorem isolated_canonical_of_counts (principal : I)
    (h : d.TableIPatternHypotheses principal)
    (hcover : ∀ j, ∃ a, d.normalizedTableIRow j = row a)
    (c : Bool) (hn : ∀ a, d.tableIRowMultiplicity (row a) = solution c false a) :
    d.HasCanonicalTableIPattern principal := by
  classical
  apply d.hasCanonicalTableIPattern_of_rowMultiplicity principal h
    (solutionCase c) (solutionVariant c)
  intro r
  by_cases hr : ∃ a, row a = r
  · obtain ⟨a, rfl⟩ := hr
    exact (hn a).trans (solution_counts c a)
  · have hz : d.tableIRowMultiplicity r = 0 := by
      unfold tableIRowMultiplicity
      apply Fintype.card_eq_zero_iff.mpr
      refine ⟨fun j => ?_⟩
      obtain ⟨a, ha⟩ := hcover j.1
      exact hr ⟨a, ha.symm.trans j.2⟩
    rw [hz]
    symm
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun j => ?_⟩
    obtain ⟨a, ha⟩ := solution_covered c j.1
    exact hr ⟨a, ha.symm.trans j.2⟩

/-- Coverage and one of the four explicit count vectors give the required
principal-preserving canonical identification, in its correct orientation. -/
theorem hasCanonicalTableIPattern_or_reflect_of_isolated_solutions (principal : I)
    (h : d.TableIPatternHypotheses principal)
    (hcover : ∀ j, ∃ a, d.normalizedTableIRow j = row a)
    (hn : ∃ c o, (fun a => d.tableIRowMultiplicity (row a)) = solution c o) :
    d.HasCanonicalTableIPattern principal ∨
      d.reflectColumns.HasCanonicalTableIPattern principal := by
  obtain ⟨c, o, hn⟩ := hn
  cases o
  · left
    exact d.isolated_canonical_of_counts principal h hcover c (congrFun hn)
  · right
    apply d.reflectColumns.isolated_canonical_of_counts principal (h.reflectColumns d) ?_ c ?_
    · intro j
      obtain ⟨a, ha⟩ := hcover j
      exact ⟨reflection a, by rw [d.isolated_normalized_reflection, ha, row_reflection]⟩
    · intro a
      rw [d.isolated_multiplicity_reflection, congrFun hn (reflection a)]
      exact solution_reflection c a

end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
