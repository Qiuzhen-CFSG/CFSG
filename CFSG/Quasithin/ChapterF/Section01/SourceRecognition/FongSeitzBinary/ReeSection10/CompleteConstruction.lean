module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.LastPureConstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularLastSuzukiLinearMain

/-!
# Complete Section 10 reconstruction from the synchronized source data

Both pure endpoint commutators are proved in the actual marked quotient.
Generation of the native root groups extends them to every whole-root angular
equation. The torus, normalizer and rank-one identities then assemble the
Section 10 construction and its marked and original amalgam comparisons.
No additional endpoint equation or coefficient-field restriction is assumed.

Source: Fong--Seitz II (1974), Section 10, in the literal native triangular
Suzuki charts, including the binary parameter case.
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

/-- Both whole-root endpoint equations follow from the synchronized source data. -/
theorem synchronizedSuzukiEndEquations {n m : ℕ}
    (c : ReeSixHData Q split n m) :
    RemainingSuzukiEndEquations Q split c :=
  synchronizedSuzukiEndEquations_of_pure Q split c
    (synchronized_opposite_main_commutator Q split c)
    (synchronized_last_main_commutator Q split c)

/-- The complete native angular table over every Ree coefficient field. -/
theorem synchronizedAngularEquations {n m : ℕ}
    (c : ReeSixHData Q split n m) :
    Equations (AngularPresentation.table m) (synchronizedSourceRoot Q split c) :=
  orderedEquations_of_suzukiEnd Q split c
    (synchronizedSuzukiEndEquations Q split c)

/-- Section 10 reconstruction with no additional angular hypotheses. -/
def Section10Construction.ofSixHData {n m : ℕ}
    (c : ReeSixHData Q split n m) :
    Section10Construction Q split n m :=
  Section10Construction.ofAngular Q split c
    (synchronizedAngularEquations Q split c)

/-- Apply the marked comparison to the completed source reconstruction. -/
theorem concrete_comparison_ofSixHData {n m : ℕ}
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
        inf_le_left inf_le_right) Q.standardAmalgam)
    (c : ReeSixHData Q split n m) :
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
    (synchronizedAngularEquations Q split c)

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

/-- Complete construction on the original marked octagon. -/
def Section10Construction.ofOriginalOctagonComplete :
    Section10Construction Q split n m :=
  Section10Construction.ofSixHData Q split
    (originalOctagonInput Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁)

include Q split e h hm n hn μ₀ T hB₀ μ₁ hB₁ in
/-- The original marked octagon has the native Ree amalgam. -/
theorem original_concrete_comparison :
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
  concrete_comparison_ofSixHData Q split e
    (originalOctagonInput Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
