module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.SixHAssembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalCenters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalCommonField

/-!
# Constructing (6H) from the original natural panel markings

The faithful original panel equivalences and their whole Borel maps are
transported along the given marked amalgam. Hypothesis F.1.1 supplies
both core premises; the source proofs then construct all of ReeSixHData.
Neither relations nor a source module or model comparison are assumed.
The octagonal row, natural family pairing and odd degree remain the
preceding source-selection inputs, including n=1 and m=0.
Source: Fong--Seitz I (1973), (6H), pp.51--56.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
  (μ₀ : (parabolic L S 0 ⧸ originalPanelKernel (L := L) (S := S) 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map μ₀.toMonoidHom = normalizer (T : Set _))
  (μ₁ : (parabolic L S 1 ⧸ originalPanelKernel (L := L) (S := S) 1) ≃* SuzukiMatrixGroup m)
  (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map μ₁.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

/-- Genuine (6H) data from the original panels, without a relation-package argument. -/
def originalSourceReeSixHData :
    Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.ReeSixHData Q split n m :=
  sourceReeSixHData Q split n hn m
    (faithfulModelMarking Q e h 0 μ₀) T
    (faithfulModelMarking_borel Q e h 0 μ₀ (normalizer (T : Set _)) hB₀)
    (faithfulModelMarking Q e h 1 μ₁)
    (faithfulModelMarking_borel Q e h 1 μ₁ (normalizer (SuzukiRootSubgroup m : Set _)) hB₁)
    hm (LinearThreePresentation.borel_core_eq_bot Q e h)
    (parabolic_core_selfCentralizing Q e h 1)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal

variable {G : Type*} [Group G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
  (μ₀ : (parabolic L S 0 ⧸ originalPanelKernel (L := L) (S := S) 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map μ₀.toMonoidHom = normalizer (T : Set _))
  (μ₁ : (parabolic L S 1 ⧸ originalPanelKernel (L := L) (S := S) 1) ≃* SuzukiMatrixGroup m)
  (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map μ₁.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

/-- The same constructed input on the literal original quotient Q.q. -/
def quotientSourceReeSixHData :
    Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.ReeSixHData Q split n m :=
  originalSourceReeSixHData Q (originalMarkedIso Q) h split hm n hn m μ₀ T hB₀ μ₁ hB₁

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
