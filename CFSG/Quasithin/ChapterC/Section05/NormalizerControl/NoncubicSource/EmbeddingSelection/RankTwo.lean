module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo.SylowOvergroups
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo.Exceptional
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo.Linear
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo.Triality
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo.Ree
/-!
# Rank-two proper-overgroup adapters for C.5.13

The two rank-two source families and the small derived exceptional carriers
are re-exported at the C.5 embedding-selection boundary. Every theorem keeps
the actual local C-component and full Sylow hypotheses.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]
/-- All eight actual rank-two constructors are discharged. The original
parabolic-residual statement is used only in the triality and Ree branches. -/
theorem eq_of_rankTwo_parabolic_model
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    [IsQuasisimple B] (hmodel : LocalModels.RankTwoTheoremC L)
    (hres : IsParabolicResidual B L true) : B = L := by
  cases hmodel with
  | linear n hn hm => exact eq_of_binary_linear_three_model T hB hL hBL hn hm
  | symplectic n hn hm => exact eq_of_binary_symplectic_model T hB hL hBL hn hm
  | g2 n hn hm => exact eq_of_binary_g2_model T hB hL hBL hm
  | triality n hn hm => exact (not_parabolicResidual_of_binary_triality hres hn hm).elim
  | ree m hm he => exact (not_parabolicResidual_of_ree hres hm he).elim
  | symplectic_derived hm => exact eq_of_binary_symplectic_derived_model T hB hL hBL hm
  | g2_derived hm => exact eq_of_binary_g2_derived_model T hB hL hBL hm
  | tits hm => exact eq_of_tits_model T hB hL hBL hm
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
