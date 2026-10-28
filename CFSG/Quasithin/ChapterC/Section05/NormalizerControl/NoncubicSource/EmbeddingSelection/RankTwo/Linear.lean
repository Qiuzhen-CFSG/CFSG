module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo.SylowOvergroups
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ComponentSource.LinearThree
/-!
# The binary PSL₃ branch of the C.5.13 embedding sieve

The full-Sylow-overgroup geometry for the actual PSL₃ carrier rules out a
proper quasisimple local C-component. No whole-Borel hypothesis is added.
Source: Aschbacher–Smith A.3.12(2) and C.5.13, printed pp.47,162–163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ChapterA.Section03 ChapterB.ComponentRecognition.SylowOvergroups
variable {G : Type*} [Group G] [Finite G]
theorem eq_of_binary_linear_three_model
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    [IsQuasisimple B] {n : ℕ} (hn : 1 ≤ n)
    (hmodel : ClassicalGroup.IsPSL L 3 (2 ^ n)) : B = L := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  exact eq_of_proper_sylow_fitting_bound T hB hL hBL
    (properSylowFittingBound_of_equiv e
      (ChapterC.RankOne.ChiProduct.ComponentSource.linearThree_properSylowFittingBound
        F (by omega) hF))
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
