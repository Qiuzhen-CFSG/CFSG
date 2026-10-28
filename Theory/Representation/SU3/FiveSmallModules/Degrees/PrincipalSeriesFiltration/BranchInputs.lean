module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.Inputs

/-!
# The two finite principal-series calculations at five

The trivial character is expected to have factors of degrees 1, 20 and 104;
a nontrivial cubic character has factors of degrees 21 and 84. Each predicate
below requires a filtration of the actual induction quotient over the original
coefficient field, with simple successive quotient actions. Neither predicate
asserts that such a filtration has been constructed.

The two calculations are independent. Their assembly uses the proved character
coverage; it retains both predicates until their concrete filtrations, field
transports and action identifications are supplied.

Source: the principal-series approach to Guralnick–Malle, *Classification of
2F-modules I*, Proposition 4.3, p.10; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups
namespace Representation.SU3.FiveSmallModules.Degrees
universe u v

/-- The untwisted calculation, retaining every matrix and coefficient field. -/
def TrivialPrincipalSeriesFiltrations : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2],
      FactorDegreeFiltration {1, 20, 104}
        (ind (standardBorel J).subtype (scalarCharacter (1 : standardBorel J →* Kˣ)))

/-- The twisted calculation for each nontrivial cubic character that exists
in the original coefficient field. No GF(4) assumption is added. -/
def CubicPrincipalSeriesFiltrations : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (χ : standardBorel J →* Kˣ),
      χ ≠ 1 → (∀ b, χ b ^ 3 = 1) →
      FactorDegreeFiltration {21, 84}
        (ind (standardBorel J).subtype (scalarCharacter χ))

end Representation.SU3.FiveSmallModules.Degrees
