module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.Construction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularCommuteFamily

/-!
# Commuting entries retained by the Section 10 construction

The `ofAngular` constructor uses the synchronized positive charts.  This leaf
records the two commuting angular pairs already proved on the marked quotient
at the exact construction boundary, without claiming any of the remaining
ordered angular equations.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4.RootPresentationRecognition
open ReeF4.RootPresentationRecognition.AngularPresentation
open Theory.GroupTheory.OrderedRootPresentation
open ReeF4.CentralCovers.TwoPrimary
open CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

/-- The `A₀/B₂` commuting equation at the constructed chart boundary. -/
theorem Section10Construction.ofAngular_A0_B2_commute
    (E : OrderedRootPresentation.Equations
      (AngularPresentation.table m) (synchronizedSourceRoot Q split c))
    (a : CoefficientField m) (y z : CoefficientField m) :
    Commute
      (((Section10Construction.ofAngular Q split c E).d.chart (.inl 0) a : X ⧸ Q.D))
      (((Section10Construction.ofAngular Q split c E).d.chart (.inr 2) (y,z) : X ⧸ Q.D)) := by
  exact synchronized_A0_B2_commute Q split c a y z

/-- The `A₂/B₁` commuting equation at the constructed chart boundary. -/
theorem Section10Construction.ofAngular_A2_B1_commute
    (E : OrderedRootPresentation.Equations
      (AngularPresentation.table m) (synchronizedSourceRoot Q split c))
    (a : CoefficientField m) (y z : CoefficientField m) :
    Commute
      (((Section10Construction.ofAngular Q split c E).d.chart (.inl 2) a : X ⧸ Q.D))
      (((Section10Construction.ofAngular Q split c E).d.chart (.inr 1) (y,z) : X ⧸ Q.D)) := by
  exact synchronized_A2_B1_commute Q split c a y z

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
