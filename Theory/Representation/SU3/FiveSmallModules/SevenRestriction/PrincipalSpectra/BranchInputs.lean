module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Inputs

/-!
# Simple-factor inputs for the principal-series seven-spectra

The finite calculation identifies the small simple sections of the literal
Borel-induced modules and their characteristic polynomials. An independent
extension argument must then treat arbitrary small sections, including a
twenty-dimensional simple factor extended by a trivial line.

The element-order version keeps both the group and operator order hypotheses.
The operator hypothesis excludes sections consisting entirely of trivial
factors. `PrincipalSpectra` removes the group-order hypothesis by replacing an
actor with an element of order seven inducing exactly the same operator.

These are input contracts, not assertions that the finite calculation or the
extension argument has been established. Source: Guralnick–Malle,
*Classification of 2F-modules I*, Proposition 4.3, pp.10–11; Aschbacher–Smith
K.2, printed p.453.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Polynomial

namespace Representation.SU3.FiveSmallModules.SevenRestriction

universe u v

/-- The small simple factors, with their integer spectral multiplicities.
This quantifies over actual irreducible subquotients of the induced action;
it does not assume absolute irreducibility or a central kernel. -/
def PrincipalSeriesSmallFactorSevenSpectra : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (χ : standardBorel J →* Kˣ)
      (S : Subrepresentation (ind (standardBorel J).subtype (scalarCharacter χ)))
      (T : Subrepresentation S.toRepresentation),
      T.quotientRepresentation.IsIrreducible →
      Module.finrank K (S.toSubmodule ⧸ T.toSubmodule) ≤ 21 →
      ∀ x : standardGroup J, orderOf x = 7 →
        (Module.finrank K (S.toSubmodule ⧸ T.toSubmodule) = 1 ∧
          (T.quotientRepresentation x).charpoly = X - C 1) ∨
        ((Module.finrank K (S.toSubmodule ⧸ T.toSubmodule) = 20 ∨
          Module.finrank K (S.toSubmodule ⧸ T.toSubmodule) = 21) ∧
          (T.quotientRepresentation x).charpoly =
            sevenSpectrum K (Module.finrank K (S.toSubmodule ⧸ T.toSubmodule)))

/-- The spectral assertion for all eligible subquotients, restricted to actors
which themselves have order seven. The operator must still have order seven. -/
def PrincipalSeriesElementSevenSpectra : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (χ : standardBorel J →* Kˣ)
      (S : Subrepresentation (ind (standardBorel J).subtype (scalarCharacter χ)))
      (T : Subrepresentation S.toRepresentation),
      (Module.finrank K (S.toSubmodule ⧸ T.toSubmodule) = 20 ∨
        Module.finrank K (S.toSubmodule ⧸ T.toSubmodule) = 21) →
      ∀ x : standardGroup J, orderOf x = 7 →
        orderOf (T.quotientRepresentation x) = 7 →
        (T.quotientRepresentation x).charpoly =
          sevenSpectrum K (Module.finrank K (S.toSubmodule ⧸ T.toSubmodule))

end Representation.SU3.FiveSmallModules.SevenRestriction
