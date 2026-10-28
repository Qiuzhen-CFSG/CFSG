module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.BinarySourceAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SuzukiOppositeNonbinary

/-!
# The uniform pure opposite Suzuki equation

The binary source-action rigidity theorem and the nonbinary torus/additivity
theorem have the same literal native conclusion. This module exposes their
uniform case split for downstream angular and braid consumers.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory ReeF4 BenderSuzuki.MatrixGroups
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4.RootPresentationRecognition WeylPresentation SignedGeometry
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)
local notation "L" i:max a:max => synchronizedPositivePoint Q split c (Sum.inl i) a
local notation "S" i:max a:max b:max => synchronizedPositivePoint Q split c (Sum.inr i) (a,b)

/-- The pure opposite Suzuki commutator over every Ree coefficient field. -/
theorem synchronized_opposite_main_commutator (a y : CoefficientField m) :
    (S 2 y 0)⁻¹ * (S 0 a 0)⁻¹ * S 2 y 0 * S 0 a 0 =
      S 1 (a*titsEnd m y) (titsEnd m (a*titsEnd m y) * (a*titsEnd m y)) *
        L 3 ((a*titsEnd m a) * (y*titsEnd m y)) * S 3 (titsEnd m a*y) 0 := by
  by_cases hm : m = 0
  · exact BinarySourceAction.binary_opposite_main_commutator Q split c hm a y
  · exact synchronized_opposite_main_commutator_nonbinary Q split c
      (Nat.pos_of_ne_zero hm) a y

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
