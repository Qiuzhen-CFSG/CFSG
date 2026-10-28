module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.Inputs
public import Mathlib.RepresentationTheory.Invariants

/-!
# The two root-restriction calculations for SU₃(5)

For the canonical order-125 root subgroup P, the nonlinear constituents have
nontrivial central character. Their total dimension is a positive multiple
of 20 when the ambient representation has central kernel. The constituents
with trivial central character are linear. A nontrivial one has eight distinct
torus conjugates in the dual of P/Z(P), so cannot occur in dimension below eight.

The predicates below specify these two independent calculations; they do not
claim either calculation is proved. Together they give root-fixed dimension
2–4 in total dimensions 22–24. `RootEigenline` owns their final assembly with
the rational Borel-line argument.

Source: the root-group route to Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, p.10, used in Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups
open HermitianForm.OddPrimeSylow.NormalizedOuter
namespace Representation.SU3.FiveSmallModules.Degrees.RootEigenline

universe u v

/-- The literal root subgroup in `standardBorel J`. -/
abbrev standardRoot {F : Type u} [Field F] (J : HermitianForm 3 F) :
    Subgroup (standardGroup J) :=
  HermitianForm.BorelTorus.specialRoot (FormTransport.standardForm J) rfl

/-- The center of the root subgroup, embedded in the original SU group.
It is not the center of SU₃. -/
abbrev standardRootCenter {F : Type u} [Field F] (J : HermitianForm 3 F) :
    Subgroup (standardGroup J) :=
  (Subgroup.center (standardRoot J)).map (standardRoot J).subtype

/-- The total nonlinear root contribution is a positive multiple of 20.
No faithfulness on the full SU group is assumed. -/
def RootNonlinearMultiplicityInput : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
      (τ : Representation K (standardGroup J) U),
      τ.ker ≤ Subgroup.center (standardGroup J) →
      ∃ a : ℕ, 0 < a ∧ Module.finrank K U =
        Module.finrank K (Representation.invariants (τ.comp (standardRootCenter J).subtype)) + 20 * a

/-- Below dimension eight, root-center invariants are root invariants.
This requires the torus orbits on characters, not just its element orbits. -/
def RootLinearGapInput : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
      (τ : Representation K (standardGroup J) U),
      Module.finrank K (Representation.invariants
        (τ.comp (standardRootCenter J).subtype)) < 8 →
      Representation.invariants (τ.comp (standardRoot J).subtype) =
        Representation.invariants (τ.comp (standardRootCenter J).subtype)

end Representation.SU3.FiveSmallModules.Degrees.RootEigenline
