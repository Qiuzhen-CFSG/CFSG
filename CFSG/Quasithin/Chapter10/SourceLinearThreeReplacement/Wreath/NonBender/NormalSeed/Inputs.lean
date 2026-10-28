module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.Inputs

/-!
# Intrinsic interfaces for the normal-seed argument

The normal seed has elementary-nine quotient by its literal two-core.
The first obligation uses that normal subgroup and the ambient SQTK rank
bound to exclude three from each C-component. The second recognizes the
literal two-core quotient of a three-free C-component. Neither obligation
assumes quasisimplicity or a model for the component.

These propositions specify the intrinsic steps proved in `Rank` and
`Recognition`. Their application to the actual centralizer is in `Source`.
Source: Aschbacher--Smith 10.3.3, printed p.756, normal-seed paragraph.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender.NormalSeed
universe u

/-- The concrete elementary abelian group of order nine. -/
abbrev ElementaryNine := Multiplicative (Fin 2 → ZMod 3)

/-- The rank obstruction, retaining a relatively normal subgroup of the
actual ambient SQTK group and its intrinsic two-core quotient. -/
def NormalNineRankInput : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], IsSQTK KnownSimple.IsKnownSimple H →
    ∀ X : Subgroup H, X.Normal →
      Nonempty ((X ⧸ pCore 2 X) ≃* ElementaryNine) →
      ∀ I : Subgroup H, I.IsCComponent → ¬ 3 ∣ Nat.card I

/-- Recognition of the literal quotient; three-freeness is the independent
rank step's output, while quasisimplicity must be proved in this step. -/
def ThreeFreeRecognitionInput : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], IsSQTK KnownSimple.IsKnownSimple H →
    ∀ I : Subgroup H, I.IsCComponent → ¬ 3 ∣ Nat.card I →
      ClassificationModels.IsBenderModel (I ⧸ pCore 2 I)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender.NormalSeed
