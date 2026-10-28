module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuFamilyComplete
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOneExclusions
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianExclusion

/-!
# The surviving non-Mathieu action on the original chosen orbit

The source family sieve and the unitary, Suzuki and Hermitian exclusions now
discharge every input of the non-Mathieu assembly. The selected PSL₂ proof
excludes the natural action and the field-four orthogonal endpoint using the
full normalizer non-FF hypothesis. It leaves the actual marked minus orthogonal
action with exponent greater than one, on the unchanged orbit and component.

The second theorem applies this result at the original `hother` boundary of
12.2.2. Only the separate doubled and Mathieu branches remain with the normalized
non-FF assembly owner, `qt-d-1222-normalized-nonff`.

Source: Aschbacher--Smith, 3.2.9, 7.0.1 and the proof of 12.2.2,
printed pp.582--583, 695 and 795 (combined manuscript, 1 March 2004).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The complete non-Mathieu branch on the literal chosen orbit. No family
selection, model exclusion or representation transport remains as an input. -/
theorem sourceOrbit_orthogonal_of_nonMathieu_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    OrthogonalMinusAlternative D.orbitRepresentation D.orbitComponent :=
  D.sourceOrbit_orthogonal_of_nonMathieu_remaining_inputs h hmany hV hs hnm hnon
    (D.sourceOrbit_families_of_many h hmany hV hs hnm hnon)
    (D.sourceOrbit_hermitian_excluded h hmany hV hs hnm hnon)

/-- Discharge the non-Mathieu callback of the original chosen-module consumer.
The doubled and Mathieu premises belong to the separate normalized assembly. -/
theorem sourceOrbit_ff_or_orthogonal_of_nonMathieu_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hdoubled : V ≠ D.sourceOrbit →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → False)
    (hmathieu : V = D.sourceOrbit →
      ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent →
      HasMathieuCentralQuotient D.orbitComponent →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → Nonempty (G ≃* Janko4.Model)) :
    IsFFModule D.sourceOrbitNormalizerRepresentation ∨
      OrthogonalMinusAlternative D.orbitRepresentation D.orbitComponent :=
  D.sourceOrbit_ff_or_orthogonal_of_branches_of_many h hmany hdoubled hmathieu
    (D.sourceOrbit_orthogonal_of_nonMathieu_of_many h hmany)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
