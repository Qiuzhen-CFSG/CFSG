module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.BlockRecognition.Source
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellSelection.CoreEscape
/-!
# A literal source escape produces the C.1.18 block alternative

The actual Sylow-contained subgroup X and its commutators with O₂(H)
feed Campbell's source residual bound. The recognition theorem then makes
O²(H) an L₂ block or A₃ block. Equivalently, in the nonblock family every
such X remains in O₂(H); this is the placement needed in the uniform
characteristic-pair selection.

Source: Campbell II.8, printed p.38; Aschbacher–Smith C.1.18, p.126.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}

theorem InLocalClass.blockAlternative_of_noncore_commutator
    (h : InLocalClass e) (hB : IsBaumannFixed B) (X : Subgroup H)
    (hXS : X ≤ e.range) (hXQ : ¬X ≤ pCore 2 H)
    (hXF : ⁅X,pCore 2 H⁆ ≤ Campbell.F H) : BlockAlternative H :=
  h.blockAlternative_of_residual_commutator_le hB
    (h.residual_core_le_V_of_noncore_commutator hB X hXS hXQ hXF)

theorem InLocalClass.le_core_of_nonblock_commutator
    (h : InLocalClass e) (hB : IsBaumannFixed B) (hn : ¬BlockAlternative H)
    (X : Subgroup H) (hXS : X ≤ e.range)
    (hXF : ⁅X,pCore 2 H⁆ ≤ Campbell.F H) : X ≤ pCore 2 H := by
  by_contra hx
  exact hn (h.blockAlternative_of_noncore_commutator hB X hXS hx hXF)
end CFSG.Quasithin.ChapterC.GlaubermanNiles
