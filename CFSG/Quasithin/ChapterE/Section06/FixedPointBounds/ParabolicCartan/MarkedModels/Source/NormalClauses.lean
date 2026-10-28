module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import CFSG.Quasithin.ChapterE.Section02.Structure.OriginalNormal
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The literal normal-component input of the full E.2.2 alternatives

The source product and center theorem applies to the original selected
C-component. Its core is the normal core of the same unique maximal;
the center identity uses the actual component image in H/O₂(H). This
discharges both structural fields of `SingleClauses` without any model
or generation-parameter conclusion as an extra hypothesis.

Source: Aschbacher–Smith E.2.2(2), printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H] [Finite H]

/-- Both structural clauses of the actual normal-component alternative. -/
theorem source_single_clauses (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    SingleClauses (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H) := by
  have h := Structure.source_original_normal_clauses T hP hs K hK hqK hgen
  exact ⟨h.1,h.2⟩
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
