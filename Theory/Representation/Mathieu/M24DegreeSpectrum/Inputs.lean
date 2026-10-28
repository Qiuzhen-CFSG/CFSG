module

public import Theory.Mathieu.M24.Basic
public import Theory.Representation.AbsolutelyIrreducible
public import Mathlib.LinearAlgebra.Trace

/-!
# Absolute calculations for the small M₂₄ binary spectrum

The degree calculation concerns all faithful absolutely irreducible actions
of the actual Witt-design M₂₄ over finite fields of characteristic two.
The separate trace calculation concerns only degree eleven. Applied to the
Schur-field representation of a binary irreducible module, Frobenius-fixed
traces force that field to have degree one. Absolute degree forty-four
already forces field degree one in the binary window at most forty-eight.

These are unproved contracts, not a character-table classification.
`M24DegreeSpectrum` proves their scalar descent; its GM02 consumer also
removes arbitrary quasisimple central covers.

Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
M₂₄ paragraph, manuscript p.17; G. D. James, The modular characters of the
Mathieu groups, J. Algebra 27 (1973), 57–111.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum
open Sporadic.Mathieu
universe v

/-- The complete absolute degree window, without a field-of-definition claim. -/
def AbsoluteSmallSpectrum : Prop :=
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (W : Type v) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K M24 W),
    Function.Injective τ → τ.IsAbsolutelyIrreducible → Module.finrank K W ≤ 48 →
      Module.finrank K W = 11 ∨ Module.finrank K W = 44

/-- Traces of every faithful absolute degree-eleven action lie in the prime field. -/
def DegreeElevenTraceField : Prop :=
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (W : Type v) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K M24 W),
    Function.Injective τ → τ.IsAbsolutelyIrreducible → Module.finrank K W = 11 →
      ∀ g, LinearMap.trace K W (τ g) ^ 2 = LinearMap.trace K W (τ g)

end Representation.Mathieu.M24DegreeSpectrum
