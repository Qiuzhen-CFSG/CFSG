module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.Inputs

/-!
# Local calculations for the degree-twenty character comparison

After `CentralDescent`, both representations have trivial SU center and no
fixed vectors under the embedded root center. The remaining calculation can
be split at the actual Borel restriction. Extraspecial-root Clifford theory
should identify these twenty-dimensional Borel modules; the rank-one group
relations must then establish uniqueness of their extension to SU₃(5).

The two predicates specify independent proof obligations, not established
classification results. In particular, a Borel intertwiner is not by itself
an intertwiner for the whole group. `CharacterCalculation` retains the final
assembly, including the literal comparison quotient over the original field.

Source motivation: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, pp.10–11; Aschbacher–Smith K.2, printed p.453. These local
obligations are a proof route to the exhaustive calculation, not quotations
of a character-table certificate from that passage.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
open Degrees.RootEigenline
universe v

/-- Clifford-theoretic comparison on the literal root-and-torus Borel.
The central-kernel clause is in the direction that kills the SU center.
No Borel eigenline, induction occurrence, or splitting field is assumed. -/
def TwentyBorelComparison : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (U W : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
      [AddCommGroup W] [Module K W] [FiniteDimensional K W]
      (ρ : Representation K (standardGroup J) U)
      (σ : Representation K (standardGroup J) W),
      Module.finrank K U = 20 → Module.finrank K W = 20 →
      Subgroup.center (standardGroup J) ≤ ρ.ker →
      Subgroup.center (standardGroup J) ≤ σ.ker →
      invariants (ρ.comp (standardRootCenter J).subtype) = ⊥ →
      invariants (σ.comp (standardRootCenter J).subtype) = ⊥ →
      Nonempty (Representation.Equiv (ρ.comp (standardBorel J).subtype)
        (σ.comp (standardBorel J).subtype))

/-- Uniqueness of a whole-group extension of the actual degree-twenty Borel
module. The conclusion requires an SU intertwiner, not merely the supplied
Borel intertwiner; equality on generators cannot be inferred from traces. -/
def TwentyBorelExtensionRigidity : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (U W : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
      [AddCommGroup W] [Module K W] [FiniteDimensional K W]
      (ρ : Representation K (standardGroup J) U)
      (σ : Representation K (standardGroup J) W),
      Module.finrank K U = 20 → Module.finrank K W = 20 →
      Subgroup.center (standardGroup J) ≤ ρ.ker →
      Subgroup.center (standardGroup J) ≤ σ.ker →
      invariants (ρ.comp (standardRootCenter J).subtype) = ⊥ →
      invariants (σ.comp (standardRootCenter J).subtype) = ⊥ →
      Nonempty (Representation.Equiv (ρ.comp (standardBorel J).subtype)
        (σ.comp (standardBorel J).subtype)) →
      Nonempty (ρ.Equiv σ)

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
