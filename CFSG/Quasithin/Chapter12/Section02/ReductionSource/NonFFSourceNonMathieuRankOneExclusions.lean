module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOneUnitaryExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOneSuzukiExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieu

/-!
# Discharging the unitary and Suzuki branches of the non-Mathieu assembly

The literal chosen-orbit exclusions discharge both selected-family callbacks
of the existing non-Mathieu source assembly. The separate family sieve and
Hermitian row retain their own original inputs; the doubled and Mathieu
branches retain their existing boundaries. Final non-Mathieu assembly remains
with qt-d-1222-nonff-nonmathieu, and the normalized assembly with
qt-d-1222-normalized-nonff.

Source: Aschbacher--Smith 7.5.2 and 12.2.2, printed pp.700 and 795.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.NonMathieuAssembly
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The non-Mathieu assembly with both rank-one exceptional rows discharged. -/
theorem sourceOrbit_orthogonal_of_nonMathieu_remaining_inputs
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hfamilies : SourceFamilies hs) (hhermitian : HermitianRow hs → False) :
    OrthogonalMinusAlternative D.orbitRepresentation D.orbitComponent := by
  apply D.sourceOrbit_orthogonal_of_nonMathieu_inputs hs hnon hfamilies
    (fun _ hs2 hq => D.sourceOrbit_unitary_excluded h hmany hV hs hnm hnon hs2 hq)
    ?_ hhermitian
  rintro m hm ⟨e⟩
  exact D.sourceOrbit_suzuki_excluded h hmany hV hs hnm hnon hm e

/-- Both selected-family exclusions at the original normalized source boundary.
Only the independent doubled, Mathieu, family-sieve and Hermitian producers
remain as inputs to their existing final assembly owners. -/
theorem sourceOrbit_ff_or_orthogonal_of_nonMathieu_remaining_inputs_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hdoubled : V ≠ D.sourceOrbit →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → False)
    (hmathieu : V = D.sourceOrbit →
      ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent →
      HasMathieuCentralQuotient D.orbitComponent →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → Nonempty (G ≃* Janko4.Model))
    (hfamilies : V = D.sourceOrbit →
      ∀ hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent,
      ¬ HasMathieuCentralQuotient D.orbitComponent →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → SourceFamilies hs)
    (hhermitian : V = D.sourceOrbit →
      ∀ hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent,
      ¬ HasMathieuCentralQuotient D.orbitComponent →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → HermitianRow hs → False) :
    IsFFModule D.sourceOrbitNormalizerRepresentation ∨
      OrthogonalMinusAlternative D.orbitRepresentation D.orbitComponent := by
  apply D.sourceOrbit_ff_or_orthogonal_of_nonMathieu_inputs_of_many h hmany
    hdoubled hmathieu hfamilies ?_ ?_ hhermitian
  · intro hV hs hnm hnon s hs2 hq
    exact D.sourceOrbit_unitary_excluded h hmany hV hs hnm hnon hs2 hq
  · rintro hV hs hnm hnon m hm ⟨e⟩
    exact D.sourceOrbit_suzuki_excluded h hmany hV hs hnm hnon hm e
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
