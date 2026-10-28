module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.Construction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularFirstEquation

/-!
# Section 10 construction consumer for the first ordered tail

This leaf transports the proved `B₀/B₃` ordered-tail equation to the
`ofAngular` construction boundary.  It exposes one actual construction
application while leaving the other ordered angular equations in the explicit
finite equation package.
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

theorem Section10Construction.ofAngular_B0_B3_ordered_tail
    (E : OrderedRootPresentation.Equations
      (AngularPresentation.table m) (synchronizedSourceRoot Q split c))
    (a b y z : CoefficientField m) :
    ((Section10Construction.ofAngular Q split c E).d.chart (.inr 0) (a,b) : X ⧸ Q.D) *
      ((Section10Construction.ofAngular Q split c E).d.chart (.inr 3) (y,z) : X ⧸ Q.D) *
      (((Section10Construction.ofAngular Q split c E).d.chart (.inr 0) (a,b) : X ⧸ Q.D))⁻¹ =
    OrderedRootPresentation.word (AngularPresentation.Parameter m)
      (fun i => synchronizedSourceRoot Q split c i)
      (tail sourceOrder (.inr 0))
      ((PositiveTables.rootChartEquiv m (.inl 1) (a*y),
        (PositiveTables.rootChartEquiv m (.inr 3) (y,z),
          (PositiveTables.rootChartEquiv m (.inl 3) 0,
            (PositiveTables.rootChartEquiv m (.inr 1) (0,0),
              (PositiveTables.rootChartEquiv m (.inl 2) 0,
                (PositiveTables.rootChartEquiv m (.inr 2) (0,0),
                  (PositiveTables.rootChartEquiv m (.inl 0) 0, PUnit.unit)))))))) := by
  have h0 :
      ((Section10Construction.ofAngular Q split c E).d.chart (.inr 0) (a,b) : X ⧸ Q.D) =
        synchronizedPositivePoint Q split c (.inr 0) (a,b) := by rfl
  have h3 :
      ((Section10Construction.ofAngular Q split c E).d.chart (.inr 3) (y,z) : X ⧸ Q.D) =
        synchronizedPositivePoint Q split c (.inr 3) (y,z) := by rfl
  rw [h0, h3]
  rw [← synchronizedSourceRoot_field Q split c (.inr 0) (a,b),
    ← synchronizedSourceRoot_field Q split c (.inr 3) (y,z)]
  exact synchronized_B0_B3_ordered_tail Q split c a b y z

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
