module

public import Mathlib.GroupTheory.PresentedGroup

/-!
# The four-relator presentation used for PSL₃(4)

The words are those printed in Campbell–Havas–Ramsay–Robertson,
*Nice efficient presentations for all small simple groups and their covers*,
LMS J. Comput. Math. 7 (2004), Table 2 and §5.11:
`a^5`, `b^5`, `(ab)^3`, and `a²B²ABaB²abAB`, where capitals denote inverses.
Source: https://staff.itee.uq.edu.au/havas/2004chrr.pdf.

This module defines the abstract presentation and proves its fifth-power
relations. It does not assert its identification with the matrix group.
An abstract order bound and a surjective matrix comparison are the separate
inputs to that identification.
-/

@[expose] public section

namespace Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation

/-- Free words in the two displayed generators. -/
abbrev Word := FreeGroup (Fin 2)

/-- The first free generator. -/
def a : Word := FreeGroup.of 0

/-- The second free generator. -/
def b : Word := FreeGroup.of 1

/-- The length-thirteen mixed relator in Table 2. -/
def mixed : Word :=
  a ^ 2 * (b ^ 2)⁻¹ * a⁻¹ * b⁻¹ * a * (b ^ 2)⁻¹ * a * b * a⁻¹ * b⁻¹

/-- Exactly the four printed relators. -/
def relators : Set Word := {a ^ 5, b ^ 5, (a * b) ^ 3, mixed}

/-- The abstract presented group, before comparison with the matrix model. -/
abbrev Presentation := PresentedGroup relators

/-- Both distinguished generators satisfy the fifth-power relation. -/
theorem generator_pow_five (i : Fin 2) :
    (PresentedGroup.of (rels := relators) i) ^ 5 = 1 := by
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · change (PresentedGroup.mk relators) a ^ 5 = 1
    rw [← map_pow]
    apply PresentedGroup.one_of_mem
    simp [relators]
  · change (PresentedGroup.mk relators) b ^ 5 = 1
    rw [← map_pow]
    apply PresentedGroup.one_of_mem
    simp [relators]

end Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation
