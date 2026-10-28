module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo.ParabolicResidual
public import Theory.SpecificGroups.Triality.ParabolicSolvableFitting
public import Theory.SpecificGroups.Triality.Model.QTKE
/-!
# The original triality parabolic row in C.5.13

Keep A.3.12's actual parabolic-residual hypothesis. The smaller group in
C.5.13 is quasisimple, whereas every proper triality Borel overgroup has
solvable generalized Fitting subgroup. This excludes the literal row.
Source: Aschbacher–Smith A.3.12(2) and C.5.13, pp.47,162–163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]
theorem not_parabolicResidual_of_binary_triality {B L : Subgroup G}
    [IsQuasisimple B] (hres : IsParabolicResidual B L true)
    {n : ℕ} (hn : 1 ≤ n) (hmodel : Triality.Standard.IsTrialityGroupAt (2 ^ n) L) : False := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff L n (by omega)).mp hmodel
  exact not_parabolicResidual_of_model hres e
    (Triality.Standard.Parabolics.proper_borel_overgroup_fitting_isSolvable n (by omega))
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
