module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.OriginalComparisons
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.Model
public import Theory.GroupTheory.Amalgam.Reversal

/-!
# The published U₄ and general-q U₅ marked models

The ambient projective comparisons restrict to the existing concrete model
amalgams, including their exact overlap definitions, in both orientations.
No model tag substitutes for the matrix equivalence. U₄ uses its published
GF(2^(2m)) carrier and U₅ retains Model q without a q=4 restriction.
Source: DGS, Groups and Graphs, Theorem D, printed p.224;
Aschbacher–Smith F.1.12, printed pp.263–264.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation

namespace FourModel
open GreenBook.LieModels.UnitaryFour
variable (m : ℕ) (hm : 1≤m)
local notation "E" => MatrixField m
local notation "σ" => fieldConj m
local notation "hσ" => fieldConj_involutive m hm

/-- Exact change from the intersection description to the published full overlap. -/
def forwardFlag : RankTwoAmalgam.Iso
    (MarkedAmalgam.flag (pointParabolic m hm) (planeParabolic m hm) 0) (amalgam m hm) where
  left := MulEquiv.refl _
  middle := MulEquiv.subgroupCongr (exact_overlap m hm)
  right := MulEquiv.refl _
  left_commutes _ := rfl
  right_commutes _ := rfl

def reverseFlag : RankTwoAmalgam.Iso
    (MarkedAmalgam.flag (pointParabolic m hm) (planeParabolic m hm) 1) (amalgam m hm).reverse where
  left := MulEquiv.refl _
  middle := MulEquiv.subgroupCongr (exact_overlap m hm)
  right := MulEquiv.refl _
  left_commutes _ := rfl
  right_commutes _ := rfl

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (hrot : rotationOrder Q=4)

def forwardComparison (d : FourData Q split 0 σ hσ) :
    RankTwoAmalgam.Iso Q.standardAmalgam (amalgam m hm) :=
  (d.markedIso σ hσ hrot).trans (forwardFlag m hm)

def reverseComparison (d : FourData Q split 1 σ hσ) :
    RankTwoAmalgam.Iso Q.standardAmalgam (amalgam m hm).reverse :=
  (d.markedIso σ hσ hrot).trans (reverseFlag m hm)

@[simp] theorem forwardComparison_middle (d : FourData Q split 0 σ hσ) (b : Q.tits.B) :
    ((forwardComparison m hm Q split hrot d).middle b : ProjectiveGroup m hm)=
      (d.projectiveEquiv σ hσ hrot).symm b := rfl
@[simp] theorem reverseComparison_middle (d : FourData Q split 1 σ hσ) (b : Q.tits.B) :
    ((reverseComparison m hm Q split hrot d).middle b : ProjectiveGroup m hm)=
      (d.projectiveEquiv σ hσ hrot).symm b := rfl
end FourModel

namespace FiveModel
open GreenBook.UnitaryFive
variable {q : ℕ} (M : Model q) (κ : M.F) (hκ : κ+M.form.conj κ=1)
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (hrot : rotationOrder Q=4)
variable (hZ : center (X ⧸ Q.D)=⊥)

/-- This is the actual general-q projective model, without a q=4 specialization. -/
def forwardComparison (d : FiveData Q split 0 M.form) :
    RankTwoAmalgam.Iso Q.standardAmalgam M.amalgam :=
  d.markedIso M.form κ hκ M.matrix hrot hZ

def reverseComparison (d : FiveData Q split 1 M.form) :
    RankTwoAmalgam.Iso Q.standardAmalgam M.amalgam.reverse :=
  d.markedIso M.form κ hκ M.matrix hrot hZ

@[simp] theorem forwardComparison_middle (d : FiveData Q split 0 M.form) (b : Q.tits.B) :
    ((forwardComparison M κ hκ Q split hrot hZ d).middle b : M.Carrier)=
      (d.projectiveEquiv M.form κ hκ M.matrix hrot hZ).symm b := rfl
@[simp] theorem reverseComparison_middle (d : FiveData Q split 1 M.form) (b : Q.tits.B) :
    ((reverseComparison M κ hκ Q split hrot hZ d).middle b : M.Carrier)=
      (d.projectiveEquiv M.form κ hκ M.matrix hrot hZ).symm b := rfl
end FiveModel
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
