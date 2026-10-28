module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Averaging

/-!
# The remaining linear calculation for the degree-twenty extension

The averaged Bruhat equations determine the Weyl action when their coefficient
operator is injective. This predicate asks precisely for that injectivity on
all endomorphisms of the original twenty-dimensional space. It assumes no
irreducibility, splitting field, coordinates or equivalence with a model.
It is an outstanding input, not an asserted theorem.

`twenty_borel_extension_rigidity_of_rootCosetInjectivity` applies it to the
literal representation in `TwentyBorelExtensionRigidity`, retaining the
provided Borel equivalence and discharging all other extension steps.
Source of the equations: Huppert II.10.12; see `Averaging`.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups
open HermitianForm.OddPrimeSylow.NormalizedOuter
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
open Degrees.RootEigenline
universe v

/-- Uniform injectivity of the actual Borel-coefficient Bruhat operator. -/
def TwentyRootCosetInjectivity : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
      (ρ : Representation K (standardGroup J) U),
      Module.finrank K U = 20 →
      Subgroup.center (standardGroup J) ≤ ρ.ker →
      invariants (ρ.comp (standardRootCenter J).subtype) = ⊥ →
      Function.Injective (ExtensionRigidity.rootCosetOperator (FormTransport.standardForm J) rfl ρ)

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
