module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Factorization.Source
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.SourceInputs

/-!
# Source consumers of the covered factorization

The universal factorization field used in the solvable 13.8.5 branch is
proved for its original natural-section setup. The 13.8.21 quotient-order
transport now uses that result on the unchanged original groups and
cover projection, with no factorization premise.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.CubicOrders
variable {G : Type*} [Group G] [Finite G]

/-- The exact `EarlierLocalInputs.covered_factorization` source field. -/
theorem earlier_covered_factorization :
    ∀ (L T V W₁ W₃ : Subgroup G),
      LocalAction.NaturalSetup L T V W₁ W₃ → one L T W₁ = plus L T W₁ ⊔ zero L := by
  intro L T V W₁ W₃ d
  exact CoverFactorization.source_factorization d

/-- The original 13.8.21 residual-quotient transport with 13.2.2(3) discharged. -/
theorem source_plus_core_card_eq_model
    {L T V V₁ V₃ : Subgroup G} (d : LocalAction.NaturalSetup L T V V₁ V₃) :
    Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) =
      Nat.card (Representation.Hexacode.CubicLocalModel.commutatorResidual d.point (coverSylow d) ⧸
        pCore 2 (Representation.Hexacode.CubicLocalModel.commutatorResidual d.point (coverSylow d))) :=
  plus_core_card_eq_model d (CoverFactorization.source_factorization d)

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion

end
