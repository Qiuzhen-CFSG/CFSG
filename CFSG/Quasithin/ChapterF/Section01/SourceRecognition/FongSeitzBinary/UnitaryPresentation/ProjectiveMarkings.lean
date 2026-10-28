module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.QuotientRecognition
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.MarkedAmalgam

/-!
# Full projective Borel and both unitary endpoint markings

Both quotient equivalences commute with the canonical SU→PSU maps. Their
restrictions identify the entire projective Borel and both literal flag
stabilizers with the source Borel and its marked standard parabolics.
All three subgroup maps belong to one RankTwoAmalgam.Iso, in either
orientation. The SU₅ scalar kernel is retained for arbitrary q.
Source: DGS, Groups and Graphs, Theorem D, printed p.224.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
variable {X E : Type*} [Group X] [Field E] [Finite E] [CharP E 2]
variable {P : Fin 2 → Subgroup X} {Q : MarkedQuotient P} {split : SplitData Q.tits} {i : Fin 2}
namespace FourData
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
variable (σ : E ≃+* E) (hσ : Function.Involutive σ) (d : FourData Q split i σ hσ)
variable (hm : rotationOrder Q=4)
local notation "J" => form E σ hσ

theorem projectiveHom_comp :
    (d.projectiveEquiv σ hσ hm).toMonoidHom.comp (project E J)=d.modelHom σ hσ := by
  ext g
  exact d.projectiveEquiv_project σ hσ hm g

theorem projective_point : ((pointParabolicSU E J).map (project E J)).map
    (d.projectiveEquiv σ hσ hm).toMonoidHom=Q.tits.standardParabolic {Q.simple i} := by
  rw [Subgroup.map_map,d.projectiveHom_comp]
  exact d.modelHom_point σ hσ hm

theorem projective_plane : ((planeParabolicSU E J).map (project E J)).map
    (d.projectiveEquiv σ hσ hm).toMonoidHom=Q.tits.standardParabolic {Q.simple (1-i)} := by
  rw [Subgroup.map_map,d.projectiveHom_comp]
  exact d.modelHom_plane σ hσ hm

theorem projective_borel : ((borelSU E J).map (project E J)).map
    (d.projectiveEquiv σ hσ hm).toMonoidHom=Q.tits.B := by
  rw [Subgroup.map_map,d.projectiveHom_comp]
  exact d.modelHom_borel σ hσ hm

/-- Both endpoints and the full overlap are restrictions of the ONE projective equivalence. -/
def markedIso : RankTwoAmalgam.Iso Q.standardAmalgam
    (MarkedAmalgam.flag ((pointParabolicSU E J).map (project E J))
      ((planeParabolicSU E J).map (project E J)) i) :=
  MarkedAmalgam.fromSource Q _ _ i (d.projectiveEquiv σ hσ hm)
    (d.projective_point σ hσ hm) (d.projective_plane σ hσ hm)

@[simp] theorem markedIso_left (a : Q.tits.standardParabolic {Q.simple 0}) :
    ((d.markedIso σ hσ hm).left a : PSU E J)=(d.projectiveEquiv σ hσ hm).symm a := rfl
@[simp] theorem markedIso_middle (b : Q.tits.B) :
    ((d.markedIso σ hσ hm).middle b : PSU E J)=(d.projectiveEquiv σ hσ hm).symm b := rfl
@[simp] theorem markedIso_right (a : Q.tits.standardParabolic {Q.simple 1}) :
    ((d.markedIso σ hσ hm).right a : PSU E J)=(d.projectiveEquiv σ hσ hm).symm a := rfl
end FourData
namespace FiveData
open Theory.SpecificGroups.UnitaryFive
variable (J : HermitianForm 5 E) (κ : E) (hκ : κ+J.conj κ=1) (hJ : J.form=1)
variable (d : FiveData Q split i J) (hm : rotationOrder Q=4) (hZ : center (X ⧸ Q.D)=⊥)

theorem projectiveHom_comp :
    (d.projectiveEquiv J κ hκ hJ hm hZ).toMonoidHom.comp (project J)=d.modelHom J κ hκ hJ := by
  ext g
  exact d.projectiveEquiv_project J κ hκ hJ hm hZ g

theorem projective_line : (lineParabolic J).map (d.projectiveEquiv J κ hκ hJ hm hZ).toMonoidHom=
    Q.tits.standardParabolic {Q.simple i} := by
  change ((specialStabilizer J (line E)).map (project J)).map _=_
  rw [Subgroup.map_map,d.projectiveHom_comp]
  exact d.modelHom_line J κ hκ hJ hm

theorem projective_plane : (planeParabolic J).map (d.projectiveEquiv J κ hκ hJ hm hZ).toMonoidHom=
    Q.tits.standardParabolic {Q.simple (1-i)} := by
  change ((specialStabilizer J (plane E)).map (project J)).map _=_
  rw [Subgroup.map_map,d.projectiveHom_comp]
  exact d.modelHom_plane J κ hκ hJ hm

theorem projective_borel : (lineParabolic J ⊓ planeParabolic J).map
    (d.projectiveEquiv J κ hκ hJ hm hZ).toMonoidHom=Q.tits.B := by
  change (Theory.SpecificGroups.UnitaryFive.parabolic J (line E) ⊓ Theory.SpecificGroups.UnitaryFive.parabolic J (plane E)).map _=_
  rw [←parabolic_inf J (line E) (plane E),Subgroup.map_map,d.projectiveHom_comp,←FiveCells.borel_eq_flag J κ hκ hJ]
  exact d.modelHom_borel J κ hκ hJ hm

/-- The actual PSU₅ flag amalgam, with its entire scalar quotient and both orientations. -/
def markedIso : RankTwoAmalgam.Iso Q.standardAmalgam
    (MarkedAmalgam.flag (lineParabolic J) (planeParabolic J) i) :=
  MarkedAmalgam.fromSource Q _ _ i (d.projectiveEquiv J κ hκ hJ hm hZ)
    (d.projective_line J κ hκ hJ hm hZ) (d.projective_plane J κ hκ hJ hm hZ)

@[simp] theorem markedIso_left (a : Q.tits.standardParabolic {Q.simple 0}) :
    ((d.markedIso J κ hκ hJ hm hZ).left a : ProjectiveSpecialUnitaryMatrixGroup J)=
      (d.projectiveEquiv J κ hκ hJ hm hZ).symm a := rfl
@[simp] theorem markedIso_middle (b : Q.tits.B) :
    ((d.markedIso J κ hκ hJ hm hZ).middle b : ProjectiveSpecialUnitaryMatrixGroup J)=
      (d.projectiveEquiv J κ hκ hJ hm hZ).symm b := rfl
@[simp] theorem markedIso_right (a : Q.tits.standardParabolic {Q.simple 1}) :
    ((d.markedIso J κ hκ hJ hm hZ).right a : ProjectiveSpecialUnitaryMatrixGroup J)=
      (d.projectiveEquiv J κ hκ hJ hm hZ).symm a := rfl
end FiveData
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
