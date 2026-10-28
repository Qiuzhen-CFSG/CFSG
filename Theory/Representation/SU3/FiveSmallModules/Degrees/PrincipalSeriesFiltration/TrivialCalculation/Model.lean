module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.PermutationFlag
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.BranchInputs
public import ABG.Basic

/-!
# The canonical middle-factor calculation

The canonical matrix group is the antidiagonal special unitary group over
GF(25); its Borel is the actual upper-root-and-torus join. The permutation
space consists of functions on its left cosets. The remaining middle-flag
predicate keeps every finite characteristic-two coefficient field.

These definitions specify a finite calculation; they assert no certificate.
The independent Borel-preserving field comparison is proved in
`FieldTransport`, and the parent assembly discharges the end factors.
Source motivation: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, p.10; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

open scoped MonoidAlgebra
open BenderSuzuki.MatrixGroups
namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation
universe v
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Identity-Gram input over GF(25); `standardGroup` replaces its Gram matrix
by the antidiagonal one and retains fifth-power conjugation. -/
noncomputable abbrev canonicalInputForm := ABG.unitaryForm 3 5 1 (by decide)
noncomputable abbrev CanonicalGroup := standardGroup canonicalInputForm
noncomputable abbrev canonicalBorel : Subgroup CanonicalGroup := standardBorel canonicalInputForm
abbrev CanonicalPoints := CanonicalGroup ⧸ canonicalBorel
noncomputable instance : Fintype CanonicalPoints := Fintype.ofFinite _

/-- The group comparison must carry the actual Borel, not just its order. -/
def BorelFieldTransport : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∃ e : standardGroup J ≃* CanonicalGroup,
      ∀ g, e g ∈ canonicalBorel ↔ g ∈ standardBorel J

/-- Only the two middle simple factors remain in the canonical calculation.
The quantifier keeps the original characteristic-two coefficient field. -/
def CanonicalMiddleFlags : Prop :=
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2],
    MiddleFlag (K := K) (G := CanonicalGroup) (Ω := CanonicalPoints)
end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation
