module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Exceptional
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Classical.LinearSource
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Classical.SymplecticSource
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Exceptional.Triality.Source
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Exceptional.G2.OuterDescent
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Sp4Four
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.OddBender
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms
public import Theory.SpecificGroups.Triality.StandardTwoRank.Derived
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.Source

/-!
# Source rank-two inspection

The linear, symplectic, G₂ and triality rows are now connected to their
concrete involution calculations.  The Ree and Tits rows use the proved full Suzuki projection and genuine
root-parabolic fixed table. The original Sp₄(4) field case uses its complete
source geometry. No classification or geometry premise remains.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo
open ClassificationModels
universe u

/-- The complete exceptional inspection on the actual source model carriers. -/
theorem exceptionalInspection_source
    : ExceptionalInspection.{u} := by
  apply exceptionalInspection_of_model_facts
    (hg2 := Exceptional.G2.outerFixedModels)
    (htinner := Exceptional.Triality.innerFixedRank_source)
    (htouter := Exceptional.Triality.outerFixedModels_source)
  · intro m hm
    exact (Triality.Standard.TwoRank.binaryCarrier_simple_and_perfect m hm).1
  · intro m hm _ _ a ha
    obtain ⟨g, hg⟩ := ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.inner_of_sq_eq_one
      hm a (by simpa only [ha] using pow_orderOf_eq_one a)
    exact ⟨g, hg.symm⟩
  · intro m hm _ _
    exact ⟨ReeF4.ConverseParabolics.suzukiProjection hm,
      ReeF4.ConverseParabolics.suzukiProjection_ker_isPGroup hm⟩
  · intro a ha
    obtain ⟨P,hP,_,hfix⟩ := _root_.Tits.InvolutionRootGeometry.involution_fixed_parabolic a ha
    exact ⟨P,hP,hfix⟩

/-- The complete source rank-two exclusion, including the genuine Sp₄(4) field case. -/
theorem rankTwoExclusion_source
    {G : Type u} [Group G] [Finite G] (T : Sylow 2 G) (M V : Subgroup G)
    [IsElementaryAbelian 2 V] :
    RankTwoExclusion T M V := by
  apply rankTwoExclusion_of_inspections
    (hlinear := Classical.linearInspection)
    (hsymplectic := Classical.symplecticInspection)
    (hexceptional := exceptionalInspection_source)
    (hfield := Sp4Four.symplecticFieldSourceExclusion T M V)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo
