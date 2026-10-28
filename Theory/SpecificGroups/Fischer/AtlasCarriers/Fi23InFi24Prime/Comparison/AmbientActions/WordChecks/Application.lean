module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions

/-!
# Orbit application of the staged short-word certificates

The numerical reduction supplies both candidate intertwinings required by the
existing orbit-membership theorem. Agreement with the original ambient generators
remains separate, exactly as in `AmbientActions`.
Source: GLS3 Table 5.3v and the literal `WordSetup` candidate formulas.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient

/-- Actual orbit application: the five finite word checks discharge the two
numerical premises of `labelMap_mem_suborbit_of_ambient_certificates`. The
source-generator comparison remains the parent's separate obligation. -/
theorem labelMap_mem_suborbit_of_auxiliary_checks
    (hgen : ∀ c x, letterMap c x = (letterValue c).val x)
    (hinv : ∀ c x, letterMap (inverseLetter c) (letterMap c x) = x)
    (hu : ∀ i, wordMap letterMap false uLetters (labelMap i) = labelMap (WordChecks.uMap i))
    (hv : ∀ i, wordMap letterMap false vLetters (labelMap i) = labelMap (WordChecks.vMap i))
    (hw : ∀ i, wordMap letterMap false wLetters (labelMap i) = labelMap (WordChecks.wMap i))
    (hr : ∀ i, wordMap letterMap false rLetters (labelMap i) = labelMap (WordChecks.rMap i))
    (hs : ∀ i, wordMap letterMap false sLetters (labelMap i) = labelMap (WordChecks.sMap i)) :
    ∀ i, labelMap i ∈ suborbit :=
  labelMap_mem_suborbit_of_ambient_certificates hgen
    (candidateAMap_apply_labelMap_of_auxiliary_checks hinv hv hr hw)
    (candidateBMap_apply_labelMap_of_auxiliary_checks hinv hu hv hw hs)

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient
