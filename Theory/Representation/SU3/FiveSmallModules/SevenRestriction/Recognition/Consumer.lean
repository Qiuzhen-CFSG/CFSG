module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition

/-!
# Applying the recognition branches to the order-seven spectrum

The assembled recognition supplies the actual equivalence used by
`charpoly_of_principal_series_inputs`. The independent spectral calculation
is then transported on the original representation and the original group
element. The conditional branch consumer is retained. The proved recognition
discharges both branch inputs in `charpoly_of_principal_series_spectra`,
leaving only the independent spectral calculation explicit.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

public section

open BenderSuzuki.MatrixGroups

namespace Representation.SU3.FiveSmallModules.SevenRestriction

universe u v
open Degrees.RootEigenline

/-- The recognition branches feed the existing spectral consumer using its
literal induced modules, quotient actions and intertwining equivalences. -/
theorem charpoly_of_recognition_branches
    (hnonlinear : RootNonlinearMultiplicityInput.{u, v})
    (htwenty : RootCenterFreeTwentyRecognition.{u, v})
    (hspectra : PrincipalSeriesSevenSpectra.{u, v})
    {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    {K U : Type v} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K (standardGroup J) U)
    (hk : τ.ker ≤ Subgroup.center (standardGroup J))
    (hi : τ.IsAbsolutelyIrreducible)
    (hd : Module.finrank K U = 20 ∨ Module.finrank K U = 21)
    (x : standardGroup J) (hx : orderOf (τ x) = 7) :
    (τ x).charpoly = sevenSpectrum K (Module.finrank K U) :=
  charpoly_of_principal_series_inputs
    (principal_series_recognition_of_nonlinear_and_twenty hnonlinear htwenty)
    hspectra J hc hconj τ hk hi hd x hx

/-- Exhaustive recognition supplies the exact subquotient equivalence needed
by the independent spectral calculation. Only that calculation remains an input. -/
theorem charpoly_of_principal_series_spectra
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
  charpoly_of_principal_series_inputs principal_series_recognition
    hspectra J hc hconj τ hk hi hd x hx

end Representation.SU3.FiveSmallModules.SevenRestriction
