module
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Steinberg.WordCertificates.First
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Steinberg.WordCertificates.Second
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Steinberg.CentralWords
import Mathlib.Tactic.FinCases

/-!
# The complete conjugation certificate for the eleven max4 words

Both literal max4 generators have the displayed action on all eleven words.
Every equality has been checked on the original 4060-point permutation carrier
and transferred through its faithful inclusion. The center words retain the
published marking. No external computation is a mathematical premise.

Source: Aschbacher--Smith I.2.2(7), pp.412--413, and GLS3 Table 5.3r.
ATLAS provenance and word conventions are inherited from Max4Geometry.Words.
-/

namespace Rudvalis.CoveringIncidence.Max4Steinberg.WordCertificates

public theorem conjugateWordIdentities : ConjugateWordIdentities := by
  intro i j
  fin_cases i
  · exact first_words j
  · exact second_words j

end Rudvalis.CoveringIncidence.Max4Steinberg.WordCertificates
