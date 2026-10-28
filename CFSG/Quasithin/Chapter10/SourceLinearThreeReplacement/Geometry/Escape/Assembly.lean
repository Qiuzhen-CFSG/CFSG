module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.Offender
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.PairAction

/-!
# The diagonal-centralizer escape, conditional only on diagonal fusion

The whole-module TI conclusion supplies a faithful rank-four w-offender with
constant nonidentity fixed subgroups. The concrete pair-action obstruction
contradicts this. Hence the centralizer of each original central involution
escapes M once the diagonal-fusion/whole-module TI input is supplied.

`Escape.Source` discharges the diagonal-fusion input using
`Fusion.wholeModuleTIAt`. `Escape.GeometryConsumer` applies the result to the
existing centralizer-geometry assembly without an import back to that consumer.

Source: Aschbacher--Smith 10.3.2, printed p.756, PDF p.773.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The remaining first paragraph of 10.3.2 completes the escape theorem. -/
theorem escape_of_wholeModuleTI (hwhole : WholeModuleTIAt T) : EscapeAt T := by
  intro hmany L D s hz hti z hzV hzT hzord hcent
  have hTI := hwhole hmany L D s hz hti z hzV hzT hzord hcent
  obtain ⟨g,_hg,hAM,hA,hrank,hfaith,hfixed⟩ := ti_offender s hz hTI
  obtain ⟨a,ha,hane,hneq⟩ := pairFixedSpace L D s hz
    (offenderNormalizer D.fullModule g) hAM hA hrank hfaith
  exact hneq (hfixed a ha hane)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape
