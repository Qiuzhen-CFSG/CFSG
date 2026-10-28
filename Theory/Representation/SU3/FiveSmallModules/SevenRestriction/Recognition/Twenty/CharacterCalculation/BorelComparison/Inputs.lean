module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.LocalInputs

/-!
# Intertwiner inputs for the degree-twenty Borel comparison

These are two independent calculations. The extraspecial root calculation
constructs a nonzero map between the root restrictions. The torus calculation
lifts existence of such a map to the Borel after both representations kill the
SU center. It must construct a torus-fixed map; it need not extend the particular
root map supplied as input.

The assembly in `BorelComparison` proves that both Borel restrictions are
irreducible using central fusion and the minimum positive degree twenty.
Schur's lemma then turns the nonzero Borel map into an actual equivalence.
Neither predicate below assumes the desired equivalence or irreducibility.

These are local proof obligations for the route to Guralnick–Malle,
*Classification of 2F-modules I*, Proposition 4.3, pp.10–11, used in
Aschbacher–Smith K.2, printed p.453; they are not quoted source theorems.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.BorelComparison
open Degrees Degrees.RootEigenline
universe v

/-- The two root-center-free modules have a common nonlinear root constituent,
expressed by a nonzero intertwiner over the original coefficient field. -/
def TwentyRootIntertwining : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (U W : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
      [AddCommGroup W] [Module K W] [FiniteDimensional K W]
      (ρ : Representation K (standardGroup J) U)
      (σ : Representation K (standardGroup J) W),
      Module.finrank K U = 20 → Module.finrank K W = 20 →
      invariants (ρ.comp (standardRootCenter J).subtype) = ⊥ →
      invariants (σ.comp (standardRootCenter J).subtype) = ⊥ →
      ∃ f : IntertwiningMap (ρ.comp (standardRoot J).subtype)
        (σ.comp (standardRoot J).subtype), f ≠ 0

/-- Trivial SU-center action lets the torus act on root intertwiners through
a two-group. A nonzero fixed vector gives a nonzero Borel intertwiner.
No irreducibility, dimension twenty, or root-center condition is assumed. -/
def BorelIntertwinerLifting : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (U W : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
      [AddCommGroup W] [Module K W] [FiniteDimensional K W]
      (ρ : Representation K (standardGroup J) U)
      (σ : Representation K (standardGroup J) W),
      Subgroup.center (standardGroup J) ≤ ρ.ker →
      Subgroup.center (standardGroup J) ≤ σ.ker →
      (∃ f : IntertwiningMap (ρ.comp (standardRoot J).subtype)
        (σ.comp (standardRoot J).subtype), f ≠ 0) →
      ∃ f : IntertwiningMap (ρ.comp (standardBorel J).subtype)
        (σ.comp (standardBorel J).subtype), f ≠ 0

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.BorelComparison
