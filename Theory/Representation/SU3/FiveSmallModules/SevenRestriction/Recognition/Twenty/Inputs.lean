module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Inputs
public import Mathlib.RepresentationTheory.Character

/-!
# The exhaustive trace comparison needed in degree twenty

The concrete permutation flag supplies a simple twenty-dimensional section
of trivial Borel induction. The remaining exhaustive calculation compares
the trace of every representation in the recognition contract with that
section. This predicate states the calculation and does not assert it.

`TraceComparison` converts this equality into an actual equivalence over
the original coefficient field. The arbitrary representation is not assumed
to occur in the principal series, or to possess a Borel eigenline.

Source motivation: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, pp.10–11; Aschbacher–Smith K.2, printed p.453.
The cited passage states the small-degree spectrum; it does not itself
prove this exhaustive character comparison.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups

namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty

universe v
open Degrees.RootEigenline

/-- Compare an arbitrary root-center-free absolute degree-twenty module
with each actual simple degree-twenty section of trivial Borel induction.
This is a trace identity, with no equivalence or occurrence premise for `τ`. -/
def TwentyTraceComparison : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
      (τ : Representation K (standardGroup J) U),
      τ.ker ≤ Subgroup.center (standardGroup J) →
      τ.IsAbsolutelyIrreducible → Module.finrank K U = 20 →
      invariants (τ.comp (standardRootCenter J).subtype) = ⊥ →
      ∀ (S : Subrepresentation (ind (standardBorel J).subtype
          (scalarCharacter (1 : standardBorel J →* Kˣ))))
        (T : Subrepresentation S.toRepresentation),
        T.quotientRepresentation.IsIrreducible →
        Module.finrank K (S.toSubmodule ⧸ T.toSubmodule) = 20 →
        τ.character = T.quotientRepresentation.character

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
