module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.Calculations

/-!
# Independent inputs for the Hall--Janko absolute degree window

These propositions separate a literal carrier power-fusion certificate, the
small-degree exclusions, and a nonbinary trace witness in each surviving degree.
They are unproved contracts for independent calculations, not assumptions hidden
in a group instance or assertions of the modular representation catalogue.

The assembly module `AbsoluteWindow` converts power fusion into the quadratic
trace identity and combines the three inputs. Proof modules can import this
file directly, without importing that assembly.

Sources: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
p.16, and Hiss--Malle's corrected low-degree tables, characteristic-two J₂ rows.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
open Sporadic.LeechRelated.J2
universe v

/-- The concrete conjugacy calculation needed for the upper trace-field bound.
This is a contract, not a proved property of the carrier. -/
@[expose] def PowerFusion : Prop :=
  ∀ g : Carrier, IsConj (g ^ 8) (g ^ 32)

/-- The degree-completeness obligation, without any field-of-definition claim.
This proposition remains to be proved from the literal carrier. -/
@[expose] def DegreeWindow : Prop :=
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K Carrier U),
    Function.Injective τ → τ.IsAbsolutelyIrreducible → Module.finrank K U ≤ 32 →
      Module.finrank K U = 6 ∨ Module.finrank K U = 14

/-- The independent lower trace-field bound in the two surviving degrees.
No trace witness is constructed by this definition. -/
@[expose] def TraceSeparation : Prop :=
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K Carrier U),
    Function.Injective τ → τ.IsAbsolutelyIrreducible →
      (Module.finrank K U = 6 ∨ Module.finrank K U = 14) →
      ∃ g, τ.character g ^ 2 ≠ τ.character g

/-- The remaining nonbinary trace obligation after the elementary degree-six
Frobenius-descent obstruction. -/
@[expose] def FourteenTraceSeparation : Prop :=
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K Carrier U),
    Function.Injective τ → τ.IsAbsolutelyIrreducible → Module.finrank K U = 14 →
      ∃ g, τ.character g ^ 2 ≠ τ.character g

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
