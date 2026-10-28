module

public import Theory.Representation.AbsolutelyIrreducible
public import Theory.Representation.SubspaceQuotient
public import Mathlib.RepresentationTheory.Induced
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Theory.SpecificGroups.SU3.BorelTorus.Basic
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport

/-!
# Concrete principal-series inputs for the small order-seven calculation

The recognition obligation identifies every small absolute module, with central
kernel, with an actual subquotient of a Borel-induced character. This is a
composition-factor statement: it does not assert that the module is a quotient
of the whole induced module or has a Borel eigenline.

The independent finite calculation concerns only subquotients of these
specified induced actions. It supplies characteristic polynomials, retaining
integer multiplicities in characteristic two. Neither obligation is asserted
here. Their consumers transport the polynomial through an intertwining
equivalence and through a genuine central-cover map.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section
noncomputable section

open BenderSuzuki.MatrixGroups
open HermitianForm.OddPrimeSylow.NormalizedOuter
open Polynomial

namespace Representation.SU3.FiveSmallModules.SevenRestriction

universe u v

/-- The special unitary group for the literal antidiagonal form. -/
abbrev standardGroup {F : Type u} [Field F] (J : HermitianForm 3 F) :=
  (FormTransport.standardForm J).specialSubgroup

/-- The root-and-torus Borel, with the same field involution as the input form. -/
abbrev standardBorel {F : Type u} [Field F] (J : HermitianForm 3 F) :
    Subgroup (standardGroup J) :=
  HermitianForm.BorelTorus.specialBorel (FormTransport.standardForm J) rfl

/-- The one-dimensional action of an actual unit-valued Borel character. -/
def scalarCharacter {K B : Type*} [Field K] [Group B] (χ : B →* Kˣ) :
    Representation K B K :=
  (algebraMap K (Module.End K K)).toMonoidHom.comp ((Units.coeHom K).comp χ)

/-- The sixth-degree factor of `X^7 - 1`, defined over the coefficient field. -/
def sevenPolynomial (K : Type*) [Field K] : K[X] :=
  X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1

/-- Three copies of every nontrivial seventh root and the remaining fixed roots. -/
def sevenSpectrum (K : Type*) [Field K] (d : ℕ) : K[X] :=
  sevenPolynomial K ^ 3 * (X - C 1) ^ (d - 18)

/-- Exhaustive recognition by genuine subquotient equivalences. This is not
an assertion that the small module has a Borel eigenline. -/
def PrincipalSeriesRecognition : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
      (τ : Representation K (standardGroup J) U),
      τ.ker ≤ Subgroup.center (standardGroup J) →
      τ.IsAbsolutelyIrreducible →
      (Module.finrank K U = 20 ∨ Module.finrank K U = 21) →
      ∃ (χ : standardBorel J →* Kˣ)
        (S : Subrepresentation (ind (standardBorel J).subtype (scalarCharacter χ)))
        (T : Subrepresentation S.toRepresentation),
        Nonempty (τ.Equiv T.quotientRepresentation)

/-- The finite spectral calculation on literal induced modules. The order
condition is on the operator: a central lift in SU₃ need not itself have
order seven even when its operator on a quotient does. -/
def PrincipalSeriesSevenSpectra : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (χ : standardBorel J →* Kˣ)
      (S : Subrepresentation (ind (standardBorel J).subtype (scalarCharacter χ)))
      (T : Subrepresentation S.toRepresentation),
      (Module.finrank K (S.toSubmodule ⧸ T.toSubmodule) = 20 ∨
        Module.finrank K (S.toSubmodule ⧸ T.toSubmodule) = 21) →
      ∀ x : standardGroup J, orderOf (T.quotientRepresentation x) = 7 →
        (T.quotientRepresentation x).charpoly =
          sevenSpectrum K (Module.finrank K (S.toSubmodule ⧸ T.toSubmodule))

end Representation.SU3.FiveSmallModules.SevenRestriction
