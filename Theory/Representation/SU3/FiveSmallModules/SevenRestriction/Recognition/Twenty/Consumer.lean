module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Consumer

/-!
# Applying the degree-twenty trace route to the spectral consumer

The actual recognition equivalence supplies the degree-twenty branch of
`charpoly_of_recognition_branches`. The degree-twenty-one argument and the
nonlinear-root and principal-series spectral inputs retain their existing
owners. No trace identity is used as a substitute for integer spectral
multiplicities: the characteristic polynomial travels through the proved
representation equivalence.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

public section

open BenderSuzuki.MatrixGroups

namespace Representation.SU3.FiveSmallModules.SevenRestriction

universe v
open Degrees.RootEigenline Degrees.TrivialCalculation Twenty

/-- The degree-twenty trace route supplies the exact branch consumed by
the existing order-seven characteristic-polynomial argument. -/
theorem charpoly_of_twenty_trace_and_middle_flags
    (hnonlinear : RootNonlinearMultiplicityInput.{0, v})
    (htrace : TwentyTraceComparison.{v})
    (hcard : Nat.card CanonicalPoints = 126)
    (hmiddle : CanonicalMiddleFlags.{v})
    (hspectra : PrincipalSeriesSevenSpectra.{0, v})
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    {K U : Type v} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K (standardGroup J) U)
    (hk : τ.ker ≤ Subgroup.center (standardGroup J))
    (hi : τ.IsAbsolutelyIrreducible)
    (hd : Module.finrank K U = 20 ∨ Module.finrank K U = 21)
    (x : standardGroup J) (hx : orderOf (τ x) = 7) :
    (τ x).charpoly = sevenSpectrum K (Module.finrank K U) :=
  charpoly_of_recognition_branches hnonlinear
    (root_center_free_twenty_recognition_of_trace_and_middle_flags htrace hcard hmiddle)
    hspectra J hc hconj τ hk hi hd x hx

/-- The proved degree-twenty recognition discharges that branch of the
spectral consumer. Only the independent nonlinear-root and principal-series
spectral calculations remain explicit. -/
theorem charpoly_of_nonlinear_and_principal_series_spectra
    (hnonlinear : RootNonlinearMultiplicityInput.{0, v})
    (hspectra : PrincipalSeriesSevenSpectra.{0, v})
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    {K U : Type v} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K (standardGroup J) U)
    (hk : τ.ker ≤ Subgroup.center (standardGroup J))
    (hi : τ.IsAbsolutelyIrreducible)
    (hd : Module.finrank K U = 20 ∨ Module.finrank K U = 21)
    (x : standardGroup J) (hx : orderOf (τ x) = 7) :
    (τ x).charpoly = sevenSpectrum K (Module.finrank K U) :=
  charpoly_of_recognition_branches hnonlinear root_center_free_twenty_recognition
    hspectra J hc hconj τ hk hi hd x hx

end Representation.SU3.FiveSmallModules.SevenRestriction
