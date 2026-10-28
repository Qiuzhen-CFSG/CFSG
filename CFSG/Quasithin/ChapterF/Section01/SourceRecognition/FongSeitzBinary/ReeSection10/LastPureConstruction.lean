module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularEndExtension
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SuzukiOppositeMain
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.FinalOrderedConsumer

/-!
# Section 10 reconstruction from the last pure commutator

The uniform source opposite Suzuki equation discharges the first premise of
the simultaneous endpoint extension. Only the literal Suzuki-linear main-curve
identity remains. Whole-root generation then supplies every angular equation
and the marked comparison, with no additional opposite-root hypothesis.

Source: Fong--Seitz II (1974), Section 10, (10.23)--(10.41).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open MarkedLocal ReeSource
open ReeF4.RootPresentationRecognition
open Theory.GroupTheory.OrderedRootPresentation
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  {n m : ℕ} (c : ReeSixHData Q split n m)

/-- The uniform opposite source theorem removes its endpoint premise. -/
theorem synchronizedSuzukiEndEquations_of_lastPure
    (hlast : SuzukiLastPureEquation Q split c) :
    RemainingSuzukiEndEquations Q split c :=
  synchronizedSuzukiEndEquations_of_pure Q split c
    (synchronized_opposite_main_commutator Q split c) hlast

/-- All angular equations require only the final literal main-curve identity. -/
theorem synchronizedAngularEquations_of_lastPure
    (hlast : SuzukiLastPureEquation Q split c) :
    Equations (AngularPresentation.table m) (synchronizedSourceRoot Q split c) :=
  synchronizedAngularEquations_of_pureEnd Q split c
    (synchronized_opposite_main_commutator Q split c) hlast

/-- The final source construction after discharging the opposite Suzuki branch. -/
def Section10Construction.ofLastPureCommutator
    (hlast : SuzukiLastPureEquation Q split c) :
    Section10Construction Q split n m :=
  Section10Construction.ofAngular Q split c
    (synchronizedAngularEquations_of_lastPure Q split c hlast)

/-- Apply the marked comparison with only the final pure source equation. -/
theorem concrete_comparison_of_lastPure
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
        inf_le_left inf_le_right) Q.standardAmalgam)
    (hlast : SuzukiLastPureEquation Q split c) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
        inf_le_left inf_le_right)
      (GreenBook.LieModels.ReeFour.amalgam m)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
        inf_le_left inf_le_right)
      (GreenBook.LieModels.ReeFour.amalgam m).reverse) :=
  concrete_comparison_ofAngular Q split e c
    (synchronizedAngularEquations_of_lastPure Q split c hlast)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
