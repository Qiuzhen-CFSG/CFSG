module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Injectivity.Coordinates
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Realization.Actors

/-!
# Reference representations needed by the Bruhat certificate

It suffices to realize the marked matrices on one actual SU representation
for each pair of fields. The established Borel comparison then transfers
its basis to the arbitrary representation in the injectivity contract.
The finite table-field construction and entrywise field transport are
separate obligations, allowing the latter to be proved with the former
as an explicit hypothesis. Neither predicate asserts its own existence.

Source of the literal actors: Huppert II.10.12. The candidate matrices and
coset-model provenance are recorded in `source/README.md`.
-/

@[expose] public section
open BenderSuzuki.MatrixGroups
open HermitianForm.OddPrimeSylow.NormalizedOuter
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
open Degrees.RootEigenline
universe v

namespace ExtensionRigidity.Injectivity

/-- A single genuine reference action with the marked Bruhat coefficients.
Dimension twenty is built into its carrier; no group or module recognition
conclusion is assumed. -/
structure ReferenceModel {F : Type} [Field F] (J : HermitianForm 3 F)
    (K : Type v) [Field K] where
  representation : Representation K (standardGroup J) (Fin 20 → K)
  center_le_ker : Subgroup.center (standardGroup J) ≤ representation.ker
  rootCenter_invariants :
    invariants (representation.comp (standardRootCenter J).subtype) = ⊥
  coordinates : Coordinates (FormTransport.standardForm J) rfl representation

end ExtensionRigidity.Injectivity

/-- Reference models over every original matrix and coefficient field. -/
def TwentyBruhatReferenceModels : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2],
      Nonempty (ExtensionRigidity.Injectivity.ReferenceModel J K)

/-- The finite model calculation over the already defined polynomial field
GF(5)[x]/(x²-x+2), uniform only in the coefficient field. -/
def TableBruhatModels : Prop :=
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2],
    Nonempty (ExtensionRigidity.Injectivity.ReferenceModel
      Degrees.TrivialCalculation.MiddleFactors.Realization.tableForm K)

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
