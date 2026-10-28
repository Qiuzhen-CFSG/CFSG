module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.Induction
public import Theory.Representation.FactorDegreeFiltration
public import Theory.SpecificGroups.SU3.BorelTorus.Basic
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport

/-!
# Structural inputs for the PSU₃(5) absolute degree exclusions

The root-group calculation supplies a Borel eigenline in degrees 22–24.
The independent finite calculation supplies actual simple-factor filtrations
of the induced Borel characters, of degree 126 in this model. Frobenius
reciprocity and the existing filtration theorem then exclude those degrees.

These predicates do not assert the existence of their witnesses. The final
source owner must prove both and obtain the actual covering map from the
universal-cover theorem. The standard Borel retains the input field involution;
the assembly transports arbitrary Hermitian forms by a genuine basis change.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
p.10; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups
open HermitianForm.OddPrimeSylow.NormalizedOuter

namespace Representation.SU3.FiveSmallModules.Degrees

universe u v

/-- The actual antidiagonal special unitary group, retaining the input involution. -/
abbrev standardGroup {F : Type u} [Field F] (J : HermitianForm 3 F) :=
  (FormTransport.standardForm J).specialSubgroup

/-- The actual root-and-torus Borel in the standard-form group. -/
abbrev standardBorel {F : Type u} [Field F] (J : HermitianForm 3 F) :
    Subgroup (standardGroup J) :=
  HermitianForm.BorelTorus.specialBorel (FormTransport.standardForm J) rfl

/-- A Borel eigenline in the three degrees that must be excluded.
The kernel may be central: the action pulled back from a source cover need
not be faithful on SU₃. -/
def RootEigenlineInput : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
      (τ : Representation K (standardGroup J) U),
      τ.ker ≤ Subgroup.center (standardGroup J) →
      τ.IsAbsolutelyIrreducible → 22 ≤ Module.finrank K U →
      Module.finrank K U ≤ 24 →
      ∃ (χ : standardBorel J →* Kˣ) (v : U),
        v ≠ 0 ∧ ∀ b : standardBorel J, τ b v = (χ b : K) • v

/-- Degrees allowed in the literal principal-series filtrations. -/
def principalSeriesDegrees : Set ℕ := {1, 20, 21, 84, 104}

/-- The finite calculation is a filtration of every induced Borel character,
with actual simple quotient actions. No character table or universal
small-degree assertion is included as a field of the witness. -/
def PrincipalSeriesFiltrations : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (χ : standardBorel J →* Kˣ),
      FactorDegreeFiltration principalSeriesDegrees
        (ind (standardBorel J).subtype (scalarCharacter χ))

end Representation.SU3.FiveSmallModules.Degrees
