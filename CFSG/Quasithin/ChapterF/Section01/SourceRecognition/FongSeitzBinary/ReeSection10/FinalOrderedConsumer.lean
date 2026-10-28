module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.FinalConstruction

/-!
# Final marked Section 10 equation assembly

The checked angular rows compose to a full
`OrderedRootPresentation.Equations` witness once the two remaining end pairs
`(0,6)` and `(0,7)` are supplied. This boundary feeds the general Ree/F4
comparison; the preceding three-pair consumers are retained.
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

/-- Compose every checked angular family with the residual mixed rows. -/
theorem orderedEquations_of_final
    {n m : ℕ} (c : ReeSixHData Q split n m)
    (E : RemainingAfterFinalEquations Q split c) :
    OrderedRootPresentation.Equations (AngularPresentation.table m)
      (synchronizedSourceRoot Q split c) := by
  exact synchronizedAngularEquations_of_remaining Q split c
    (remainingAngularEquations_of_next Q split c
      (remainingAfterNextEquations_of_adjacent Q split c
        (remainingAfterAdjacentEquations_of_short Q split c
          (remainingAfterShortEquations_of_linear Q split c
            (remainingAfterLinearEquations_of_final Q split c E)))))

/-- The general Ree/F4 ordered-pair consumer on the completed marked input. -/
theorem concrete_comparison_of_final
    {n m : ℕ}
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
        inf_le_left inf_le_right) Q.standardAmalgam)
    (c : ReeSixHData Q split n m)
    (E : RemainingAfterFinalEquations Q split c) :
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
  concrete_comparison_ofAngular Q split e c (orderedEquations_of_final Q split c E)

/-- All angular equations from the two remaining Suzuki end rows. -/
theorem orderedEquations_of_suzukiEnd
    {n m : ℕ} (c : ReeSixHData Q split n m)
    (E : RemainingSuzukiEndEquations Q split c) :
    OrderedRootPresentation.Equations (AngularPresentation.table m)
      (synchronizedSourceRoot Q split c) :=
  orderedEquations_of_final Q split c
    (remainingAfterFinalEquations_of_suzukiEnd Q split c E)

/-- The Ree/F4 comparison requiring only the two remaining Suzuki end rows. -/
theorem concrete_comparison_of_suzukiEnd
    {n m : ℕ}
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
        inf_le_left inf_le_right) Q.standardAmalgam)
    (c : ReeSixHData Q split n m)
    (E : RemainingSuzukiEndEquations Q split c) :
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
  concrete_comparison_ofAngular Q split e c (orderedEquations_of_suzukiEnd Q split c E)

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

/-- Apply the same ordered-pair consumer to the original marked octagon. -/
theorem original_concrete_comparison_of_final
    (E : RemainingAfterFinalEquations Q split
      (originalOctagonInput Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁)) :
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
  concrete_comparison_of_final Q split e
    (originalOctagonInput Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁) E

/-- The original marked octagon comparison from the two Suzuki end equations. -/
theorem original_concrete_comparison_of_suzukiEnd
    (E : RemainingSuzukiEndEquations Q split
      (originalOctagonInput Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁)) :
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
  concrete_comparison_of_suzukiEnd Q split e
    (originalOctagonInput Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁) E

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
