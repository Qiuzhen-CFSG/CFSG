module

public import Theory.SpecificGroups.Triality.InvolutionFixedRank
public import Theory.SpecificGroups.Triality.InvolutionTwoComponents
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Exceptional.Triality

/-!
# The complete binary triality exclusion in E.6.23

Apply the proved inner derived-rank bound and the genuine outer fixed-group
descent to the original involution. Simplicity of every smaller triality
carrier includes the binary endpoint. No inner-rank, outer-descent or small
carrier premise remains in the fixed-six exclusion.

Source: Aschbacher–Smith E.6.23, printed pp.253–254, using F.1.12(I)(4)
and 16.1.4(1),(4), `refs/quasithin.pdf`.
-/

public section
open Subgroup Theory.GroupTheory
open Triality.Standard
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Exceptional.Triality

/-- The complete inner involution family required by the original exclusion. -/
theorem innerFixedRank_source : InnerFixedRank := by
  intro n hn _ _ a ha hi
  exact _root_.Triality.Standard.InvolutionFixedRank.inner_fixed_derived_threeRank_le_one
    n hn a ha hi

/-- The complete outer involution family, with the exact half-exponent equality. -/
theorem outerFixedModels_source : OuterFixedModels := by
  intro n hn _ _ a ha hi
  exact _root_.Triality.Standard.InvolutionTwoComponents.binary_outer_fixed_equiv n hn a ha hi

/-- No involution in any genuine binary triality carrier has the forbidden fixed six. -/
theorem excludesFixedSix_source (n : ℕ) (hn : 0 < n) :
    ExcludesFixedSix (BinaryCarrier n hn) :=
  excludesFixedSix_of_involution_data innerFixedRank_source outerFixedModels_source
    (fun _ _ => inferInstance) n hn

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Exceptional.Triality
