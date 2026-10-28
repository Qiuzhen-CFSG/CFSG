module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.ProjectiveMarkings
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.MarkedLocal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.Irreducibility

/-!
# Original unitary comparisons and the literal source quotient

The original local characteristic-two premise transfers through its marked
endpoint and kills the source Borel core, hence its center. Composing the
constructed projective equivalence with the original marked quotient gives
both endpoint maps and the whole-overlap map. The generated-source variant
retains exactly Q.q, while the numerator of the general marking may be the
universal completion. Source equations and generation remain the independent
source-coordinate owner's premises.
Source: DGS, Groups and Graphs, Theorem D, printed p.224, and
Aschbacher–Smith F.1.1–3, printed pp.259–260.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
variable {G X E : Type*} [Group G] [Group X] [Field E] [Finite E] [CharP E 2]
variable {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P)
variable (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
variable (hlocal : HypothesisF11 L S) (split : SplitData Q.tits)

include e hlocal split in
/-- The actual original local characteristic-two premise kills the source
center. No source simplicity or additional centerlessness input is needed. -/
theorem source_center_eq_bot : center (X ⧸ Q.D)=⊥ := by
  apply split.center_eq_bot_of_borel_core
  apply le_bot_iff.mp
  have hc := Q.parabolic_normalCore_eq_bot split 0
    (MarkedLocal.parabolic_core_selfCentralizing Q e hlocal 0)
  exact hc ▸ Subgroup.normalCore_mono (Q.tits.B_le_standardParabolic {Q.simple 0})

variable (hm : rotationOrder Q=4) {i : Fin 2}
namespace FourOriginal
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
variable (σ : E ≃+* E) (hσ : Function.Involutive σ) (d : FourData Q split i σ hσ)
local notation "J" => form E σ hσ

def comparison : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (MarkedAmalgam.flag ((pointParabolicSU E J).map (project E J))
      ((planeParabolicSU E J).map (project E J)) i) := e.trans (d.markedIso σ hσ hm)

@[simp] theorem comparison_left (a : parabolic L S 0) :
    ((comparison Q e split hm σ hσ d).left a : PSU E J)=
      (d.projectiveEquiv σ hσ hm).symm (e.left a : X ⧸ Q.D) := rfl
@[simp] theorem comparison_middle (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((comparison Q e split hm σ hσ d).middle b : PSU E J)=
      (d.projectiveEquiv σ hσ hm).symm (e.middle b : X ⧸ Q.D) := rfl
@[simp] theorem comparison_right (a : parabolic L S 1) :
    ((comparison Q e split hm σ hσ d).right a : PSU E J)=
      (d.projectiveEquiv σ hσ hm).symm (e.right a : X ⧸ Q.D) := rfl

/-- The original generated-source specialization retains its literal quotient. -/
def originalComparison (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hm₀ : rotationOrder Q₀=4) (d₀ : FourData Q₀ split₀ i σ hσ) :=
  comparison Q₀ (originalMarkedIso Q₀) split₀ hm₀ σ hσ d₀

@[simp] theorem originalComparison_middle (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hm₀ : rotationOrder Q₀=4) (d₀ : FourData Q₀ split₀ i σ hσ)
    (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((originalComparison σ hσ Q₀ split₀ hm₀ d₀).middle b : PSU E J)=
      (d₀.projectiveEquiv σ hσ hm₀).symm (Q₀.q ⟨b,parabolic_le_generated 0 b.property.1⟩) := by
  rw [originalComparison,comparison_middle,originalMarkedIso_middle_apply]
@[simp] theorem originalComparison_left (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hm₀ : rotationOrder Q₀=4) (d₀ : FourData Q₀ split₀ i σ hσ) (a : parabolic L S 0) :
    ((originalComparison σ hσ Q₀ split₀ hm₀ d₀).left a : PSU E J)=
      (d₀.projectiveEquiv σ hσ hm₀).symm (Q₀.q ⟨a,parabolic_le_generated 0 a.property⟩) := by
  rw [originalComparison,comparison_left,originalMarkedIso_left_apply]

@[simp] theorem originalComparison_right (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hm₀ : rotationOrder Q₀=4) (d₀ : FourData Q₀ split₀ i σ hσ) (a : parabolic L S 1) :
    ((originalComparison σ hσ Q₀ split₀ hm₀ d₀).right a : PSU E J)=
      (d₀.projectiveEquiv σ hσ hm₀).symm (Q₀.q ⟨a,parabolic_le_generated 1 a.property⟩) := by
  rw [originalComparison,comparison_right,originalMarkedIso_right_apply]

end FourOriginal

namespace FiveOriginal
open Theory.SpecificGroups.UnitaryFive
variable (J : HermitianForm 5 E) (κ : E) (hκ : κ+J.conj κ=1) (hJ : J.form=1)
variable (d : FiveData Q split i J)

def quotientEquiv : ProjectiveSpecialUnitaryMatrixGroup J ≃* (X ⧸ Q.D) :=
  d.projectiveEquiv J κ hκ hJ hm (source_center_eq_bot Q e hlocal split)

def comparison : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (MarkedAmalgam.flag (lineParabolic J) (planeParabolic J) i) :=
  e.trans (d.markedIso J κ hκ hJ hm (source_center_eq_bot Q e hlocal split))

@[simp] theorem comparison_left (a : parabolic L S 0) :
    ((comparison Q e hlocal split hm J κ hκ hJ d).left a : ProjectiveSpecialUnitaryMatrixGroup J)=
      (quotientEquiv Q e hlocal split hm J κ hκ hJ d).symm (e.left a : X ⧸ Q.D) := rfl
@[simp] theorem comparison_middle (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((comparison Q e hlocal split hm J κ hκ hJ d).middle b : ProjectiveSpecialUnitaryMatrixGroup J)=
      (quotientEquiv Q e hlocal split hm J κ hκ hJ d).symm (e.middle b : X ⧸ Q.D) := rfl
@[simp] theorem comparison_right (a : parabolic L S 1) :
    ((comparison Q e hlocal split hm J κ hκ hJ d).right a : ProjectiveSpecialUnitaryMatrixGroup J)=
      (quotientEquiv Q e hlocal split hm J κ hκ hJ d).symm (e.right a : X ⧸ Q.D) := rfl

/-- The general-q original quotient comparison, with source centerlessness discharged. -/
def originalComparison (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hm₀ : rotationOrder Q₀=4) (d₀ : FiveData Q₀ split₀ i J) :=
  comparison Q₀ (originalMarkedIso Q₀) hlocal split₀ hm₀ J κ hκ hJ d₀

@[simp] theorem originalComparison_middle (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hm₀ : rotationOrder Q₀=4) (d₀ : FiveData Q₀ split₀ i J)
    (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((originalComparison hlocal J κ hκ hJ Q₀ split₀ hm₀ d₀).middle b : ProjectiveSpecialUnitaryMatrixGroup J)=
      (quotientEquiv Q₀ (originalMarkedIso Q₀) hlocal split₀ hm₀ J κ hκ hJ d₀).symm
        (Q₀.q ⟨b,parabolic_le_generated 0 b.property.1⟩) := by
  rw [originalComparison,comparison_middle,originalMarkedIso_middle_apply]
@[simp] theorem originalComparison_left (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hm₀ : rotationOrder Q₀=4) (d₀ : FiveData Q₀ split₀ i J) (a : parabolic L S 0) :
    ((originalComparison hlocal J κ hκ hJ Q₀ split₀ hm₀ d₀).left a : ProjectiveSpecialUnitaryMatrixGroup J)=
      (quotientEquiv Q₀ (originalMarkedIso Q₀) hlocal split₀ hm₀ J κ hκ hJ d₀).symm (Q₀.q ⟨a,parabolic_le_generated 0 a.property⟩) := by
  rw [originalComparison,comparison_left,originalMarkedIso_left_apply]

@[simp] theorem originalComparison_right (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hm₀ : rotationOrder Q₀=4) (d₀ : FiveData Q₀ split₀ i J) (a : parabolic L S 1) :
    ((originalComparison hlocal J κ hκ hJ Q₀ split₀ hm₀ d₀).right a : ProjectiveSpecialUnitaryMatrixGroup J)=
      (quotientEquiv Q₀ (originalMarkedIso Q₀) hlocal split₀ hm₀ J κ hκ hJ d₀).symm (Q₀.q ⟨a,parabolic_le_generated 1 a.property⟩) := by
  rw [originalComparison,comparison_right,originalMarkedIso_right_apply]

end FiveOriginal
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
