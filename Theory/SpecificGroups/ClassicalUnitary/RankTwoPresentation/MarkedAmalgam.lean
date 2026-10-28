module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.MarkedWeyl
public import Theory.GroupTheory.Amalgam.RankTwo

/-!
# Both oriented marked amalgams from one ambient equivalence

Restrictions of one group equivalence give the two endpoint maps and the
map on their ENTIRE intersection. The source Borel is recovered from the
two literal standard parabolics. This transport retains both inclusion
squares and both choices of point orientation; all model-recognition
premises are discharged by the unitary presentation applications.
Source: the marked amalgam conclusion of DGS, Theorem D, printed p.224.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.MarkedAmalgam
variable {M X : Type*} [Group M] [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (A C : Subgroup M) (i : Fin 2)

def leftGroup : Subgroup M := if i=0 then A else C
def rightGroup : Subgroup M := if i=0 then C else A

def flag : RankTwoAmalgam (leftGroup A C i) (↥(A ⊓ C)) (rightGroup A C i) :=
  .ofSubgroups _ _ _ (by
    dsimp [leftGroup]
    split
    · exact inf_le_left
    · exact inf_le_right) (by
    dsimp [rightGroup]
    split
    · exact inf_le_right
    · exact inf_le_left)

variable (e : M ≃* (X ⧸ Q.D))
variable (hA : A.map e.toMonoidHom=Q.tits.standardParabolic {Q.simple i})
variable (hC : C.map e.toMonoidHom=Q.tits.standardParabolic {Q.simple (1-i)})

include hA hC in
theorem map_overlap : (A ⊓ C).map e.toMonoidHom=Q.tits.B := by
  rw [Subgroup.map_inf _ _ _ e.injective,hA,hC]
  fin_cases i
  · exact Q.standard_intersection
  · change Q.tits.standardParabolic {Q.simple 1} ⊓ Q.tits.standardParabolic {Q.simple 0}=Q.tits.B
    rw [inf_comm]
    exact Q.standard_intersection

include hA hC in
theorem map_left : (leftGroup A C i).map e.toMonoidHom=Q.tits.standardParabolic {Q.simple 0} := by
  fin_cases i
  · exact hA
  · exact hC

include hA hC in
theorem map_right : (rightGroup A C i).map e.toMonoidHom=Q.tits.standardParabolic {Q.simple 1} := by
  fin_cases i
  · exact hC
  · exact hA

/-- All three restrictions use precisely the SAME ambient equivalence. -/
def toSource : RankTwoAmalgam.Iso (flag A C i) Q.standardAmalgam where
  left := (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_left Q A C i e hA hC))
  middle := (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_overlap Q A C i e hA hC))
  right := (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_right Q A C i e hA hC))
  left_commutes b := by
    rw [RootCoordinates.standardAmalgam_left_eq_inclusion]
    apply Subtype.ext
    rfl
  right_commutes b := by
    rw [RootCoordinates.standardAmalgam_right_eq_inclusion]
    apply Subtype.ext
    rfl

/-- The requested source-to-model orientation. -/
def fromSource : RankTwoAmalgam.Iso Q.standardAmalgam (flag A C i) :=
  (toSource Q A C i e hA hC).symm

@[simp] theorem fromSource_left (a : Q.tits.standardParabolic {Q.simple 0}) :
    ((fromSource Q A C i e hA hC).left a : M)=e.symm a := rfl
@[simp] theorem fromSource_middle (b : Q.tits.B) :
    ((fromSource Q A C i e hA hC).middle b : M)=e.symm b := rfl
@[simp] theorem fromSource_right (a : Q.tits.standardParabolic {Q.simple 1}) :
    ((fromSource Q A C i e hA hC).right a : M)=e.symm a := rfl
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.MarkedAmalgam
