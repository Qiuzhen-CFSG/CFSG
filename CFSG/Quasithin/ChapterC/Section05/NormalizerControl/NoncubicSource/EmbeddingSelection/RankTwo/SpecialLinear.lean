module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo.Linear

/-!
# The even SL₃ cover in the C.5.13 embedding sieve

The quotient of the actual SL₃ model by its center is the actual PSL₃
carrier. Its proper full-Sylow overgroups have characteristic two. The
central-cover lifting theorem retains the complete center term in the
Fitting bound, which excludes a proper quasisimple smaller component.

Source: Aschbacher–Smith A.3.6(2), A.3.12, and C.5.13, printed pp.44–48,163.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ChapterA.Section03.SourceEmbeddings Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The binary special-linear containing model admits no proper
quasisimple smaller local C-component. -/
theorem eq_of_binary_special_linear_three_model
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    [IsQuasisimple B] [IsQuasisimple L] {n : ℕ} (hn : 0 < n)
    (hmodel : IsSL L 3 (2 ^ n)) : B = L := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let f : (L ⧸ center L) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F :=
    QuotientGroup.congr _ _ e (by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact (centerCongr e ⟨x, hx⟩).property
      · intro x hx
        exact ⟨e.symm x, (centerCongr e).symm ⟨x, hx⟩ |>.property, e.apply_symm_apply x⟩)
  exact eq_of_proper_sylow_fitting_bound T hB hL hBL
    (ChapterB.ComponentRecognition.SylowOvergroups.properSylowFittingBound_of_centralQuotient f
      (ChapterC.RankOne.ChiProduct.ComponentSource.linearThree_properSylowFittingBound F hn hF))
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
