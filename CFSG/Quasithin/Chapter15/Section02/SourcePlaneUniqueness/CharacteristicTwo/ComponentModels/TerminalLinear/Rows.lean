module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Setup
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Models

/-!
# Action contracts for the four terminal module rows

Every constructor retains an intertwiner for the specified representation.
The orthogonal row uses its literal quotient by the fixed space; the
ten-dimensional row uses the exterior square or cube, with a common
group and module identification. Dimension and group names alone are
not substitutes for these assertions.

This file defines the target of the separate recognition argument. It
does not prove that a source configuration has one of these rows.
The intended action is on Additive U, where U = [⟨ZS^X⟩,X], through
the actual projection X → X/O₂(X).

Source: Aschbacher--Smith, 15.2.23(a)--(d), printed p.1117, and
B.5.1; the exterior-square/cube identification is I.1.6(7).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open ChapterB.QuasisimpleSource
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]

/-- Actual representation alternatives, with the central quotient kept in row (c).
No occurrence, parabolic alignment, or row exclusion is asserted by this definition. -/
inductive ModuleRow (ρ : Representation (ZMod 2) D W) : Prop
  | repeatedNatural (n r : ℕ) (degree : n = 4 ∨ n = 5)
      (positive : 0 < r) (bound : r ≤ n - 1)
      (action : ActionEquiv ρ
        (repeated (linearNatural BinaryField.two n) r))
  | naturalDual (n : ℕ) (degree : n = 4 ∨ n = 5)
      (action : IsNaturalPlusDual ρ n)
  | orthogonalSix (C : Subrepresentation ρ)
      (fixed : C.toSubmodule = fixedSpace ρ ⊤)
      (action : ActionEquiv C.quotientRepresentation (alternatingNatural 8))
  | exteriorFive (r : ℕ) (degree : r = 2 ∨ r = 3)
      (irreducible : IsIrreducible ρ)
      (dimension : Module.finrank (ZMod 2) W = 10)
      (action : ActionEquiv ρ (Representation.SL5TenDimensional.exteriorAction r))

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
