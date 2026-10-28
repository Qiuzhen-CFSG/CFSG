module
public import CFSG.Quasithin.Chapter5.Section03UnitaryNativeLift.Actions
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.MarkedAction

/-!
# Exact native realization of the full common-normalizer action

Every value of the published faithful marked action lifts to an automorphism
of the native projective group. Bijective restriction forces these lifts to
form a faithful homomorphism. The endpoint and whole-middle equations retain
the original conjugation action; conjugation by the entire reduced overlap
lifts to literal native Borel conjugation, including its odd elements.

This supplies the intrinsic realization step in Aschbacher–Smith 5.3.2,
printed p.659. Ambient transfer and full-normalizer gluing are separate source
obligations. No source join is recognized here.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryNativeLift
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary
open UnitarySource
variable {G : Type*} [Group G] {L K S : Subgroup G}

/-- A coherent faithful lift of the original, unchanged marked action. -/
structure FaithfulLift {X Y Z F : Type*} [Group X] [Group Y] [Group Z] [Group F]
    {β : RankTwoAmalgam X Y Z} (a : MarkedMiddleAction L K S β)
    (r : F →* RankTwoAmalgam.Iso β β) where
  action : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →* F
  restriction_eq : r.comp action = a.action
  faithful : Function.Injective action

/-- The inverse of restriction gives the actual lift, with no image premise. -/
def faithfulLift {X Y Z F : Type*} [Group X] [Group Y] [Group Z] [Group F]
    {β : RankTwoAmalgam X Y Z} (a : MarkedMiddleAction L K S β)
    (r : F →* RankTwoAmalgam.Iso β β) (hr : Function.Bijective r) : FaithfulLift a r := by
  let h := NativeAmalgamActions.unique_lift r hr a.action
  let σ := Classical.choose h
  have hσ := (Classical.choose_spec h).1
  exact ⟨σ, hσ, NativeAmalgamActions.lift_injective r a.action a.faithful σ hσ⟩

namespace Four
open ChapterF.GreenBook.LieModels.UnitaryFour
variable (m : ℕ) (hm : 1 ≤ m)

abbrev Lift (a : MarkedMiddleAction L K S (amalgam m hm)) :=
  FaithfulLift a (Chapter5.UnitaryNativeLift.Four.restriction m hm)

/-- The full original common-normalizer action lifts in this orientation. -/
def lift (hmgt : 1 < m) (a : MarkedMiddleAction L K S (amalgam m hm)) :
    Lift m hm a :=
  faithfulLift a _ (Chapter5.UnitaryNativeLift.Four.restriction_bijective m hm hmgt)

variable {m} {hm}
variable {a : MarkedMiddleAction L K S (amalgam m hm)} (f : Lift m hm a)

/-- The supplied left map is retained pointwise. -/
theorem left (g) (x : pointParabolic m hm) :
    (f.action g).val x.val = ((a.action g).left x).val :=
  congrArg (fun z => (z.left x).val) (DFunLike.congr_fun f.restriction_eq g)

/-- The supplied whole-middle map is retained pointwise. -/
theorem middle (g) (x : overlap m hm) :
    (f.action g).val x.val = ((a.action g).middle x).val :=
  congrArg (fun z => (z.middle x).val) (DFunLike.congr_fun f.restriction_eq g)

/-- The supplied right map is retained pointwise. -/
theorem right (g) (x : planeParabolic m hm) :
    (f.action g).val x.val = ((a.action g).right x).val :=
  congrArg (fun z => (z.right x).val) (DFunLike.congr_fun f.restriction_eq g)

/-- Conjugation by every element of the full reduced overlap has its literal
native Borel lift. -/
theorem inner_action
    (b : (ChapterF.Source.parabolic ![L,K] S 0 ⊓
      ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G)) :
    f.action (inclusion a.middle_le b) =
      NativeAmalgamActions.innerMiddle (pointParabolic m hm) (planeParabolic m hm) (overlap m hm) (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)
        (a.comparison.middle b) := by
  apply NativeAmalgamActions.restriction_injective (pointParabolic m hm) (planeParabolic m hm)
    (overlap m hm) (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)
    (exact_overlap m hm) (parabolics_generate m hm)
  have he := DFunLike.congr_fun f.restriction_eq (inclusion a.middle_le b)
  change Chapter5.UnitaryNativeLift.Four.restriction m hm (f.action _) = _ at he
  refine he.trans ?_
  rw [a.inner_action]
  apply RankTwoAmalgam.Iso.ext <;> ext x <;> rfl

variable (m : ℕ) (hm : 1 ≤ m)

abbrev LiftReverse (a : MarkedMiddleAction L K S (amalgam m hm).reverse) :=
  FaithfulLift a (Chapter5.UnitaryNativeLift.Four.reverseRestriction m hm)

/-- The full original common-normalizer action lifts in this orientation. -/
def liftReverse (hmgt : 1 < m) (a : MarkedMiddleAction L K S (amalgam m hm).reverse) :
    LiftReverse m hm a :=
  faithfulLift a _ (Chapter5.UnitaryNativeLift.Four.reverseRestriction_bijective m hm hmgt)

variable {m} {hm}
variable {a : MarkedMiddleAction L K S (amalgam m hm).reverse} (f : LiftReverse m hm a)

/-- The supplied left map is retained pointwise. -/
theorem leftReverse (g) (x : planeParabolic m hm) :
    (f.action g).val x.val = ((a.action g).left x).val :=
  congrArg (fun z => (z.left x).val) (DFunLike.congr_fun f.restriction_eq g)

/-- The supplied whole-middle map is retained pointwise. -/
theorem middleReverse (g) (x : overlap m hm) :
    (f.action g).val x.val = ((a.action g).middle x).val :=
  congrArg (fun z => (z.middle x).val) (DFunLike.congr_fun f.restriction_eq g)

/-- The supplied right map is retained pointwise. -/
theorem rightReverse (g) (x : pointParabolic m hm) :
    (f.action g).val x.val = ((a.action g).right x).val :=
  congrArg (fun z => (z.right x).val) (DFunLike.congr_fun f.restriction_eq g)

/-- Conjugation by every element of the full reduced overlap has its literal
native Borel lift. -/
theorem inner_actionReverse
    (b : (ChapterF.Source.parabolic ![L,K] S 0 ⊓
      ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G)) :
    f.action (inclusion a.middle_le b) =
      NativeAmalgamActions.innerMiddle (pointParabolic m hm) (planeParabolic m hm) (overlap m hm) (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)
        (a.comparison.middle b) := by
  apply NativeAmalgamActions.reverseRestriction_injective (pointParabolic m hm) (planeParabolic m hm)
    (overlap m hm) (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)
    (exact_overlap m hm) (parabolics_generate m hm)
  have he := DFunLike.congr_fun f.restriction_eq (inclusion a.middle_le b)
  change Chapter5.UnitaryNativeLift.Four.reverseRestriction m hm (f.action _) = _ at he
  refine he.trans ?_
  rw [a.inner_action]
  apply RankTwoAmalgam.Iso.ext <;> ext x <;> rfl

variable (m : ℕ) (hm : 1 ≤ m)

end Four

namespace Five
variable (U : ChapterF.GreenBook.UnitaryFive.Model 4)

abbrev Lift (a : MarkedMiddleAction L K S (U.amalgam)) :=
  FaithfulLift a (Chapter5.UnitaryNativeLift.Five.restriction U)

/-- The full original common-normalizer action lifts in this orientation. -/
def lift (a : MarkedMiddleAction L K S (U.amalgam)) :
    Lift U a :=
  faithfulLift a _ (Chapter5.UnitaryNativeLift.Five.restriction_bijective U)

variable {U}
variable {a : MarkedMiddleAction L K S (U.amalgam)} (f : Lift U a)

/-- The supplied left map is retained pointwise. -/
theorem left (g) (x : U.leftParabolic) :
    (f.action g).val x.val = ((a.action g).left x).val :=
  congrArg (fun z => (z.left x).val) (DFunLike.congr_fun f.restriction_eq g)

/-- The supplied whole-middle map is retained pointwise. -/
theorem middle (g) (x : U.overlap) :
    (f.action g).val x.val = ((a.action g).middle x).val :=
  congrArg (fun z => (z.middle x).val) (DFunLike.congr_fun f.restriction_eq g)

/-- The supplied right map is retained pointwise. -/
theorem right (g) (x : U.rightParabolic) :
    (f.action g).val x.val = ((a.action g).right x).val :=
  congrArg (fun z => (z.right x).val) (DFunLike.congr_fun f.restriction_eq g)

/-- Conjugation by every element of the full reduced overlap has its literal
native Borel lift. -/
theorem inner_action
    (b : (ChapterF.Source.parabolic ![L,K] S 0 ⊓
      ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G)) :
    f.action (inclusion a.middle_le b) =
      NativeAmalgamActions.innerMiddle (U.leftParabolic) (U.rightParabolic) (U.overlap) inf_le_left inf_le_right
        (a.comparison.middle b) := by
  apply (Chapter5.UnitaryNativeLift.Five.restriction_bijective U).1
  have he := DFunLike.congr_fun f.restriction_eq (inclusion a.middle_le b)
  change Chapter5.UnitaryNativeLift.Five.restriction U (f.action _) = _ at he
  refine he.trans ?_
  rw [a.inner_action]
  apply RankTwoAmalgam.Iso.ext <;> ext x <;> rfl

variable (U : ChapterF.GreenBook.UnitaryFive.Model 4)

abbrev LiftReverse (a : MarkedMiddleAction L K S (U.amalgam).reverse) :=
  FaithfulLift a (Chapter5.UnitaryNativeLift.Five.reverseRestriction U)

/-- The full original common-normalizer action lifts in this orientation. -/
def liftReverse (a : MarkedMiddleAction L K S (U.amalgam).reverse) :
    LiftReverse U a :=
  faithfulLift a _ (Chapter5.UnitaryNativeLift.Five.reverseRestriction_bijective U)

variable {U}
variable {a : MarkedMiddleAction L K S (U.amalgam).reverse} (f : LiftReverse U a)

/-- The supplied left map is retained pointwise. -/
theorem leftReverse (g) (x : U.rightParabolic) :
    (f.action g).val x.val = ((a.action g).left x).val :=
  congrArg (fun z => (z.left x).val) (DFunLike.congr_fun f.restriction_eq g)

/-- The supplied whole-middle map is retained pointwise. -/
theorem middleReverse (g) (x : U.overlap) :
    (f.action g).val x.val = ((a.action g).middle x).val :=
  congrArg (fun z => (z.middle x).val) (DFunLike.congr_fun f.restriction_eq g)

/-- The supplied right map is retained pointwise. -/
theorem rightReverse (g) (x : U.leftParabolic) :
    (f.action g).val x.val = ((a.action g).right x).val :=
  congrArg (fun z => (z.right x).val) (DFunLike.congr_fun f.restriction_eq g)

/-- Conjugation by every element of the full reduced overlap has its literal
native Borel lift. -/
theorem inner_actionReverse
    (b : (ChapterF.Source.parabolic ![L,K] S 0 ⊓
      ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G)) :
    f.action (inclusion a.middle_le b) =
      NativeAmalgamActions.innerMiddle (U.leftParabolic) (U.rightParabolic) (U.overlap) inf_le_left inf_le_right
        (a.comparison.middle b) := by
  apply (Chapter5.UnitaryNativeLift.Five.reverseRestriction_bijective U).1
  have he := DFunLike.congr_fun f.restriction_eq (inclusion a.middle_le b)
  change Chapter5.UnitaryNativeLift.Five.reverseRestriction U (f.action _) = _ at he
  refine he.trans ?_
  rw [a.inner_action]
  apply RankTwoAmalgam.Iso.ext <;> ext x <;> rfl

variable (U : ChapterF.GreenBook.UnitaryFive.Model 4)

end Five

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryNativeLift
