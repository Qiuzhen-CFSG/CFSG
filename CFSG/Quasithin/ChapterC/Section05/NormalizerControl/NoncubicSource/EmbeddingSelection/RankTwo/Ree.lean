module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo.ParabolicResidual
public import Theory.SpecificGroups.ReeF4.ParabolicSolvableFitting
/-!
# The original Ree parabolic row in C.5.13

The actual model equivalence preserves the displayed parabolic residual.
A quasisimple residual would lie in the solvable generalized Fitting subgroup
of that proper Borel overgroup, which is impossible.
Source: Aschbacher–Smith A.3.12(2), C.5.13, pp.47,162–163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]
theorem not_parabolicResidual_of_ree {B L : Subgroup G}
    [IsQuasisimple B] (hres : IsParabolicResidual B L true)
    {m : ℕ} (hm : 1 ≤ m) (hmodel : LocalModels.IsReeF4At L m) : False := by
  obtain ⟨d,⟨e⟩⟩ := hmodel
  exact not_parabolicResidual_of_model hres (e.trans d.modelEquiv)
    (ReeF4.ConverseParabolics.proper_borel_overgroup_fitting_isSolvable m hm)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
