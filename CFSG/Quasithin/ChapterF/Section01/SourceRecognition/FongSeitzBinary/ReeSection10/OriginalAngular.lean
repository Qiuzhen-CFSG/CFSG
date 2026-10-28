module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.Construction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalSixHAssembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.PolygonParameters.Octagon

/-!
# Original octagon input for the remaining Section 10 equations

The checked finite-octagon square theorem discharges odd linear degree from
the original natural linear/Suzuki markings and their whole Borel maps.
The established original (6H) assembly then constructs every field of the
Section 10 input, including reflections, common field and source relations.
The five computed angular pairs are supplied internally to construction.

The remaining inputs are the selected linear/Suzuki family, positive linear
degree, the marked split octagon, and the remaining literal angular equations.
Two Suzuki panels are already excluded by the imported octagon source theorem.
No oddness, common-field equality, source-relation package or model comparison
is assumed here.

Source: Fong--Seitz I (1J), (6H), pp.6 and 51--56; Fong--Seitz II, Section 10.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open MarkedLocal ReeSource

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (n : ℕ) (hn : 0 < n) (m : ℕ)
  (μ₀ : (parabolic L S 0 ⧸ ReeSource.originalPanelKernel (L := L) (S := S) 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map μ₀.toMonoidHom = normalizer (T : Set _))
  (μ₁ : (parabolic L S 1 ⧸ ReeSource.originalPanelKernel (L := L) (S := S) 1) ≃* SuzukiMatrixGroup m)
  (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map μ₁.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

/-- Full original source input, with odd degree discharged by octagon geometry. -/
def originalOctagonInput : ReeSixHData Q split n m :=
  originalSourceReeSixHData Q e h split hm n
    (linear_degree_odd_of_octagon Q split hm 0 1 (by decide) n hn m
      (faithfulModelMarking Q e h 0 μ₀) T
      (faithfulModelMarking_borel Q e h 0 μ₀ _ hB₀)
      (faithfulModelMarking Q e h 1 μ₁)
      (faithfulModelMarking_borel Q e h 1 μ₁ _ hB₁))
    m μ₀ T hB₀ μ₁ hB₁

/-- The original marked construction consumes only the 23 outstanding angular
pairs. The octagon theorem and the five computed pairs are applied here. -/
def Section10Construction.ofOriginalOctagon
    (E : RemainingAngularEquations Q split
      (originalOctagonInput Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁)) :
    Section10Construction Q split n m :=
  Section10Construction.ofRemainingAngular Q split
    (originalOctagonInput Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁) E

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
