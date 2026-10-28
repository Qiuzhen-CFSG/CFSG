module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.TrialityNativeApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.ReducedSolvability
public import Theory.SpecificGroups.Triality.BinaryLocalSections

/-!
# All reduced triality degrees at the selected-perfect-factor consumer

The binary central parabolic is solvable, whereas both literal reduced
endpoints contain their original nonsolvable selected factors. This excludes
field degree one before native lifting. The nonbinary restoration therefore
applies to every positive degree, with the original S and selected R unchanged.

Source: DGS (1985), (15.2), pp.226–228; Aschbacher–Smith 5.2.6,
pp.650–651. This consumer exclusion does not assert general binary restoration.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open Chapter6.Source.RankOneGeneric
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 0 < m) (i : Bool)
  (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) (TrialityNative.amalgam m hm i))
include d h hTH hp hm e

/-- Exclude the binary central endpoint using the actual reduced marking. -/
theorem triality_reduced_parameter : 1 < m := by
  by_contra hgt
  have hm1 : m = 1 := by omega
  subst m
  let : Group.IsSolvable (Parabolics.parabolic (binaryParameters 1 hm) .central) :=
    BinaryLocalSections.central_parabolic_solvable
  cases i
  · let j : _ ≃* Parabolics.parabolic (binaryParameters 1 hm) .central := e.right
    exact reduced_parabolics_not_solvable d h hTH hp 1
      (Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective)
  · let j : _ ≃* Parabolics.parabolic (binaryParameters 1 hm) .central := e.left
    exact reduced_parabolics_not_solvable d h hTH hp 0
      (Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective)

/-- The original comparison at every positive degree, including the proved
binary exclusion, retains the arbitrary perfect selected R. -/
theorem concreteComparison_of_reduced_triality_all_degrees :
    Global.ConcreteAmalgamComparison (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  triality_concreteComparison_of_reduced_iso d h hTH m hm
    (triality_reduced_parameter d h hTH hp m hm i e) i e hp

/-- The same all-degree application gives the original right-core equality
and containment of the same original S in the selected R. -/
theorem triality_original_core_and_containment_all_degrees :
    (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ Global.sourceS L H ≤ R :=
  triality_original_core_and_containment_of_reduced_iso d h hTH m hm
    (triality_reduced_parameter d h hTH hp m hm i e) i e hp

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
