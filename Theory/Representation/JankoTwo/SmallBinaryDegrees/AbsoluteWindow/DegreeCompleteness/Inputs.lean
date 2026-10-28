module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.Contracts
public import Mathlib.Algebra.Group.ConjFinite

/-!
# Inputs to Hall--Janko degree completeness

The remaining modular certificate can supply the small spectrum over an
algebraically closed field directly, or construct actual pairwise inequivalent
simple actions whose number reaches the odd-order conjugacy-class bound. In
the latter route completeness follows from modular trace independence.

Neither proposition is proved here. They are independent producer interfaces;
`DegreeCompleteness` owns scalar extension and the faithful degree-window
assembly. Producers should import this file to avoid an assembly cycle.

Source: corrected Hiss--Malle Table 2, characteristic-two J₂ entries; the
application is Guralnick--Malle Proposition 5.1, manuscript p.16. The offender
hypothesis of its Table 6.7 is not assumed in either interface.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
open Sporadic.LeechRelated.J2
universe v

/-- The algebraically closed certificate to be constructed by the modular
certificate owner. No list of dimensions is asserted by this definition. -/
@[expose] def ClosedSmallDegreeSpectrum : Prop :=
  ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2]
    (U : Type v) [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    (τ : Representation F Carrier U) [τ.IsIrreducible],
    Module.finrank F U ≤ 32 →
      Module.finrank F U = 1 ∨ Module.finrank F U = 6 ∨ Module.finrank F U = 14

/-- Actual simple actions and an independent conjugacy-class bound are
sufficient certificate data. Exhaustivity is a conclusion, not a field. -/
@[expose] def SaturatingModelsExist : Prop :=
  ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2],
    ∃ (n : ℕ) (d : Fin n → ℕ)
      (ρ : ∀ i, Representation F Carrier (Fin (d i) → F)),
      (∀ i, IsIrreducible (ρ i)) ∧
      (Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j))) ∧
      Nat.card (ConjClasses.mk '' {g : Carrier | ¬ 2 ∣ orderOf g}) ≤ n ∧
      ∀ i, d i = 1 ∨ d i = 6 ∨ d i = 14 ∨ 32 < d i

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
