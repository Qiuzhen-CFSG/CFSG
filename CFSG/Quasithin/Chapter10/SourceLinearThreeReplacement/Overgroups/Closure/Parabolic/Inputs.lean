module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Preparation

/-!
# Independent calculations for the diagonal parabolic

The natural-action calculation concerns the specific point stabilizer
C_{L₀T}(z), its maximality and its actual two-core quotient. The independent
residual calculation concerns any finite Sylow overgroup with that quotient:
its two-residual has elementary cubic quotient of rank two, and the Sylow
action on the Frattini quotient is irreducible. Neither calculation is
asserted here. Their source assembly must discharge both propositions.

Source: Aschbacher--Smith 10.2.4, printed p.747, used in 10.2.11 and §10.3.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic
open Chapter3.Section02 Chapter1
variable {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)

/-- The point-stabilizer recognition from the original natural action.
This contains neither Xi membership nor the centralizer-residual identity. -/
def DiagonalRecognitionAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s),
    IsCoatom ((diagonalParabolic T L (d.first*d.second)).subgroupOf (localJoin T L)) ∧
    Nonempty (((diagonalParabolic T L (d.first*d.second)) ⧸
      pCore 2 (diagonalParabolic T L (d.first*d.second))) ≃* ParabolicWreath)

/-- Intrinsic residual and irreducibility calculation for the actual wreath quotient.
The group may be any Sylow overgroup with nontrivial two-core. -/
def WreathResidualAt : Prop :=
  ∀ P : Subgroup G, (T : Subgroup G) ≤ P → P ∈ H G →
    Nonempty ((P ⧸ pCore 2 P) ≃* ParabolicWreath) →
    (pResidual 2 P).map P.subtype ∈ Xi G (T : Subgroup G) ∧
      XiOddQuotient 3 (XiQuotient ((pResidual 2 P).map P.subtype))

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic
