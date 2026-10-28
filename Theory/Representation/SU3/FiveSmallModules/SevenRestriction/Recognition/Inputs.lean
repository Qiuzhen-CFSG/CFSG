module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Inputs
public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.Contracts

/-!
# The remaining degree-twenty recognition branch

The nonlinear root multiplicity formula forces the root-center fixed space
to be zero in degree twenty and one-dimensional in degree twenty-one.
The latter is a Borel invariant line and supplies an induced-module quotient.
The former requires recognition of an interior composition factor; an
eigenline or a quotient of the entire induced module cannot be assumed.

This predicate specifies that remaining branch with the literal root center
and induction convention. It asserts no existence theorem. The recognition
assembly discharges its additional fixed-space premise from the independent
nonlinear multiplicity calculation.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups

namespace Representation.SU3.FiveSmallModules.SevenRestriction

universe u v
open Degrees.RootEigenline

/-- Exhaustive degree-twenty recognition in the branch with no root-center
fixed vectors. The nonlinear multiplicity calculation supplies this premise;
the conclusion still requires an actual subquotient equivalence. -/
def RootCenterFreeTwentyRecognition : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
      (τ : Representation K (standardGroup J) U),
      τ.ker ≤ Subgroup.center (standardGroup J) →
      τ.IsAbsolutelyIrreducible → Module.finrank K U = 20 →
      invariants (τ.comp (standardRootCenter J).subtype) = ⊥ →
      ∃ (χ : standardBorel J →* Kˣ)
        (S : Subrepresentation (ind (standardBorel J).subtype (scalarCharacter χ)))
        (T : Subrepresentation S.toRepresentation),
        Nonempty (τ.Equiv T.quotientRepresentation)

end Representation.SU3.FiveSmallModules.SevenRestriction
