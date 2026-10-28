module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.NativeRestoration
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionExceptional

/-!
# Nonsolvability survives the literal DGS reduction

Each original selected factor is already contained in its reduced endpoint.
A solvable reduced endpoint would make that factor and its two-core quotient
solvable, contradicting the original source hypotheses. This also excludes
all eight genuinely marked exceptional parabolic rows before restoration,
including J₂ and Aut(J₂), in either orientation. No binary Ree type data is
upgraded to a parabolic comparison.

Source: DGS (1985), (15.1)–(15.3), pp.226–231; Aschbacher–Smith 5.2.6,
pp.650–651. The general J₂ extension argument is not asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
include d h hTH hp

/-- The actual reduced endpoints still contain the same nonsolvable source factors. -/
theorem reduced_parabolics_not_solvable (i : Fin 2) :
    ¬ Group.IsSolvable (Source.parabolic ![L,R]
      (SuzukiContainment.reducedSylow ![L,R] (Global.sourceS L H)) i) := by
  intro hs
  let := hs
  have hLP : ![L,R] i ≤ Source.parabolic ![L,R]
      (SuzukiContainment.reducedSylow ![L,R] (Global.sourceS L H)) i :=
    le_sup_left.trans le_sup_left
  let : Group.IsSolvable (![L,R] i) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hLP)
  exact d.parabolics_not_solvable h hp i
    (((d.hypothesisF11 h hTH).parabolic_solvable_iff_local_quotient i).mpr inferInstance)

/-- The same actual reduced pair excludes every exceptional parabolic row,
including both Hall–Janko rows, without assuming an original model marking. -/
theorem not_reduced_exceptional_parabolicModels (c : GreenBook.ExceptionalModels.Case) :
    ¬ (GreenBook.ExceptionalModels.ParabolicModel c
        (reducedAmalgam ![L,R] (Global.sourceS L H)) ∨
      GreenBook.ExceptionalModels.ParabolicModel c
        (reducedAmalgam ![L,R] (Global.sourceS L H)).reverse) := by
  rintro (he | he)
  · exact reduced_parabolics_not_solvable d h hTH hp 1
      (Global.ExceptionalComparison.right_solvable c _ he)
  · exact reduced_parabolics_not_solvable d h hTH hp 0
      (Global.ExceptionalComparison.right_solvable c _ he)

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
