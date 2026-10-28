module

public import Theory.Representation.AbsolutelyIrreducible
public import Mathlib.RepresentationTheory.Character
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair

/-!
# The precise absolute calculations for small Hall--Janko modules

These two propositions specify the remaining modular representation
calculations on the literal degree-100 carrier. The first asserts a complete
absolute degree window and its trace field. The second specifies the fixed
space of the actual cubic generator in absolute degree fourteen.

They are contracts, not assertions that the calculations have been proved.
They are separated from the scalar and ambient transports so that independent
proof modules can be imported by the final assembly without a cycle.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
manuscript p.16, and the corrected Hiss--Malle low-degree tables.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees
open Sporadic.LeechRelated.J2
open Subgroup
universe v

/-- The absolute degree and trace calculations still required from the
modular representation catalogue of the literal carrier. -/
@[expose] def AbsoluteWindowCalculations : Prop :=
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K Carrier U),
    Function.Injective τ → τ.IsAbsolutelyIrreducible → Module.finrank K U ≤ 32 →
      (Module.finrank K U = 6 ∨ Module.finrank K U = 14) ∧
      (∀ g, τ.character g ^ 4 = τ.character g) ∧
      (∃ g, τ.character g ^ 2 ≠ τ.character g)

/-- The one cubic fixed-space calculation used for the degree-28 branch.
The element is the literal ATLAS generator, not an unconnected class label. -/
@[expose] def CubicFixedSpaceCalculations : Prop :=
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K Carrier U),
    Function.Injective τ → τ.IsAbsolutelyIrreducible → Module.finrank K U = 14 →
      Module.finrank K (invariants (τ.comp (zpowers GeneratorPair.b).subtype)) ≤ 4

end Representation.JankoTwo.SmallBinaryDegrees
