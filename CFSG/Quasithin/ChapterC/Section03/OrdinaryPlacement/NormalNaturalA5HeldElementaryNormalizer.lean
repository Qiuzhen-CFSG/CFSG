module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.RankSixCertificate.CoreIdentification
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup

/-!
# Full normalizers of the two marked elementary Held cores

The literal catalogue rows 20 and 21 have already been identified with the
specified conjugates of the actual local two-cores. Transporting their full
ambient normalizer identities gives the identity in the original Bool-indexed
max3/max4 coordinates. No Sylow containment of a new subgroup is assumed.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.OrdinaryPlacement.HeldElementaryCentralizer
open Held Held.LocalPairs.PairCoverage
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel
open Held.TwoLocalCandidates.MaximalNormalizerCatalogue
open Held.TwoLocalCandidates.MaximalNormalizerCatalogue.RankSixCertificate

/-- The full Held normalizer of each marked elementary core is its literal
ATLAS local overgroup. -/
theorem normalizer_ambientWordCore (i : Bool) :
    normalizer (ambientWordCore i : Set He) = localOvergroup i := by
  have hh (k : Fin 2) : normalizer (ambientWordCore (k == 0) : Set He) =
      localOvergroup (k == 0) := by
    let e := MulAut.conj (conjugator (index k))
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_normalizer_eq_of_bijective _ e.bijective]
    have hc : (ambientWordCore (k == 0)).map e.toMonoidHom = ambient (row k) := by
      rw [ambient_eq_conjugated_pCore, ambientWordCore, wordCore_eq_pCore]
      fin_cases k <;> rfl
    rw [hc, normalizer_eq_candidateGroup
      Held.LocalPairs.SylowGeometry.Calculations.representative_isPGroup
      Held.Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup]
    fin_cases k <;> rfl
  cases i
  · exact hh 1
  · exact hh 0

end CFSG.Quasithin.ChapterC.OrdinaryPlacement.HeldElementaryCentralizer
