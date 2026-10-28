module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.ModelComparisons
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.UnitaryFourNativeApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.UnitaryFiveNativeApplication

/-!
# Reduced unitary comparisons for original extension restoration

The reduced source Borel is the whole intersection of its two endpoints.
The unitary presentations identify the same marked quotient with the actual
U₄ and general-q U₅ amalgams in either orientation. These maps supply the
reduced comparison required by the independent original-extension theorems;
no original outer two-group or odd Cartan factor is removed here.
Source: DGS, Groups and Graphs, Theorem D, p.224 and (15.2), pp.226–228;
Aschbacher–Smith F.1.12, pp.263–264.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
open DGS85.OriginalExtension
variable {G X : Type*} [Group G] [Group X]
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S)

/-- Exact conversion of the reduced whole Borel to the intersection convention. -/
def intersectionToReduced : Iso
    (ofSubgroups (parabolic L (SuzukiContainment.reducedSylow L S) 0)
      (parabolic L (SuzukiContainment.reducedSylow L S) 0 ⊓
        parabolic L (SuzukiContainment.reducedSylow L S) 1)
      (parabolic L (SuzukiContainment.reducedSylow L S) 1) inf_le_left inf_le_right)
    (reducedAmalgam L S) where
  left := MulEquiv.refl _
  middle := MulEquiv.subgroupCongr (lemma_F_1_3_6 (SuzukiContainment.reduced_hypothesis h))
  right := MulEquiv.refl _
  left_commutes _ := rfl
  right_commutes _ := rfl

variable {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P)
variable (e : Iso (reducedAmalgam L S) Q.standardAmalgam)
variable (split : SplitData Q.tits) (hrot : rotationOrder Q=4)

include h e split in
theorem reduced_source_center : center (X ⧸ Q.D)=⊥ :=
  source_center_eq_bot Q ((intersectionToReduced h).trans e)
    (SuzukiContainment.reduced_hypothesis h) split

/-- The presentation supplies the literal reduced U₄ mark consumed by the
independent original-extension construction. Neither outer extension nor
original overlap is discarded. -/
def fourReducedComparison (m : ℕ) (hm : 1≤m) (point : Bool)
    (roots : FourData Q split (if point then 0 else 1)
      (GreenBook.LieModels.UnitaryFour.fieldConj m)
      (GreenBook.LieModels.UnitaryFour.fieldConj_involutive m hm)) :
    Iso (reducedAmalgam L S) (UnitaryFourNative.amalgam m hm point) := by
  cases point
  · exact e.trans (FourModel.reverseComparison m hm Q split hrot roots)
  · exact e.trans (FourModel.forwardComparison m hm Q split hrot roots)

/-- The same reduced quotient supplies general-q U₅ recognition before the
independent original quasithin and outer-action sieves. -/
def fiveReducedComparison {q : ℕ} (M : GreenBook.UnitaryFive.Model q)
    (κ : M.F) (hκ : κ+M.form.conj κ=1) (line : Bool)
    (roots : FiveData Q split (if line then 0 else 1) M.form) :
    Iso (reducedAmalgam L S) (UnitaryFiveNative.amalgam M line) := by
  have hZ := reduced_source_center h Q e split
  cases line
  · exact e.trans (FiveModel.reverseComparison M κ hκ Q split hrot hZ roots)
  · exact e.trans (FiveModel.forwardComparison M κ hκ Q split hrot hZ roots)
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
