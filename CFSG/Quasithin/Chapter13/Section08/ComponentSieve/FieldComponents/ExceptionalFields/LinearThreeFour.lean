module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.Representation.SL3FourNaturalDual.Markings

/-!
# Concrete critical-line obstructions in 13.8.20

The explicit natural-plus-dual action of SL₃(4) has no subspace of corank two
whose commutators with a full root group lie in one binary line. The root
parameters scale every displacement through F₄, so the common binary-line
condition forces the entire root group to fix the subspace. Its fixed space
has corank four, a contradiction.

For a root plane, an independent root reduces the permitted dimension to
at most seven; the interchange involution gives the same bound. Equivariant
linear maps transport all three obstructions, including the commutator line.

These are concrete model calculations, not yet the SL₃(4) exclusion. The
source assembly must construct the marked natural-plus-dual identification
and classify the quadratic actor. The projective L₃(4) exclusion also
requires passage to the faithful irreducible action before applying B.4.5.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
13.8.20, printed p.955 (PDF p.972), using F.9.13(6) and F.9.16(2).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour
open Representation.SL3FourNaturalDual

/-- The concrete rank-two obstruction, with the common binary commutator
line required by F.9.13(6). It holds without an additional faithfulness
assumption; the source's stronger F.9.16(2) inputs therefore suffice. -/
theorem sl3_four_rank_two_root_obstruction
    (D : Submodule (ZMod 2) V) (s : V)
    (hD : Module.finrank (ZMod 2) (V ⧸ D) ≤ 2)
    (hline : ∀ a : F, ∀ d ∈ D,
      representation (root a) d - d ∈ Submodule.span (ZMod 2) {s}) : False :=
  no_root_critical_line_of_corank_two D s hD hline

/-- The two source coranks are contradictory after the quadratic actor has
been placed in the explicit matrix alternatives. This conditional result does
not assert the missing placement or natural-plus-dual identification. -/
theorem sl3_four_critical_obstruction
    {J U : Type*} [Group J] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) J U) (A : Subgroup J)
    (hshape : CriticalShapes ρ A) (D : Submodule (ZMod 2) U) (s : U)
    (hD : Module.finrank (ZMod 2) (U ⧸ D) ≤ Representation.BinaryOffender.rank A)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ Submodule.span (ZMod 2) {s}) : False :=
  critical_obstruction ρ A hshape D s hD hcomm

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour
