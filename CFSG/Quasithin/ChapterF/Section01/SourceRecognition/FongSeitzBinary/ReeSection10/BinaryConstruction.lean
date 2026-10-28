module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularEndExtension
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.BinarySourceAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.FinalOrderedConsumer

/-!
# Complete Section 10 reconstruction over the binary coefficient field

The coupled endpoint rigidity calculation proves both binary main-curve
commutators. The suffix intertwining theorem extends them to whole root
groups, completing all angular equations. The resulting Section 10 data and
marked/original amalgam comparisons have no residual endpoint premise.

Source: Fong--Seitz II (1974), Section 10, including the binary case of
(10.23)--(10.41), in the native triangular Suzuki charts.
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

/-- Both whole-root endpoint equations follow from the binary source data. -/
theorem synchronizedSuzukiEndEquations_binary {n m : ℕ}
    (c : ReeSixHData Q split n m) (hfield : m = 0) :
    RemainingSuzukiEndEquations Q split c :=
  synchronizedSuzukiEndEquations_of_pure Q split c
    (BinarySourceAction.binary_opposite_main_commutator Q split c hfield)
    (BinarySourceAction.binary_last_main_commutator Q split c hfield)

/-- The complete native angular table over the binary coefficient field. -/
theorem synchronizedAngularEquations_binary {n m : ℕ}
    (c : ReeSixHData Q split n m) (hfield : m = 0) :
    Equations (AngularPresentation.table m) (synchronizedSourceRoot Q split c) :=
  orderedEquations_of_suzukiEnd Q split c
    (synchronizedSuzukiEndEquations_binary Q split c hfield)

/-- Binary Section 10 reconstruction with no additional angular hypotheses. -/
def Section10Construction.ofBinarySixHData {n m : ℕ}
    (c : ReeSixHData Q split n m) (hfield : m = 0) :
    Section10Construction Q split n m :=
  Section10Construction.ofAngular Q split c
    (synchronizedAngularEquations_binary Q split c hfield)

/-- Apply the marked comparison to the completed binary reconstruction. -/
theorem concrete_comparison_binary {n m : ℕ}
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
        inf_le_left inf_le_right) Q.standardAmalgam)
    (c : ReeSixHData Q split n m) (hfield : m = 0) :
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
    (synchronizedAngularEquations_binary Q split c hfield)

variable
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
      inf_le_left inf_le_right) Q.standardAmalgam)
  (h : HypothesisF11 L S) (hm : rotationOrder Q = 8)
  (n : ℕ) (hn : 0 < n) (m : ℕ)
  (μ₀ : (parabolic L S 0 ⧸ ReeSource.originalPanelKernel (L := L) (S := S) 0) ≃*
    PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map μ₀.toMonoidHom =
    normalizer (T : Set _))
  (μ₁ : (parabolic L S 1 ⧸ ReeSource.originalPanelKernel (L := L) (S := S) 1) ≃*
    SuzukiMatrixGroup m)
  (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map μ₁.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

/-- Complete binary construction on the original marked octagon. -/
def Section10Construction.ofOriginalOctagonBinary (hfield : m = 0) :
    Section10Construction Q split n m :=
  Section10Construction.ofBinarySixHData Q split
    (originalOctagonInput Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁) hfield

include Q split e h hm n hn μ₀ T hB₀ μ₁ hB₁ in
/-- The original binary marked octagon has the native Ree amalgam. -/
theorem original_concrete_comparison_binary (hfield : m = 0) :
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
  concrete_comparison_binary Q split e
    (originalOctagonInput Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁) hfield

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
