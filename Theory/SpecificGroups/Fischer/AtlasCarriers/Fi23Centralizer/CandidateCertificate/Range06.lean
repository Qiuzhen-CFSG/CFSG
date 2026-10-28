module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Predicates

/-!
# Fi23 point certificates: block 6

Balanced kernel reductions certify 2048 consecutive input letters. They check
the exact generator complements, word, seventh power, square and fixed image.
Source: ATLAS F23G1-p31671B0, for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
set_option Elab.async false

set_option maxRecDepth 2000 in
theorem range48 : checkRange pointCheck 8 12288 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range49 : checkRange pointCheck 8 12544 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range50 : checkRange pointCheck 8 12800 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range51 : checkRange pointCheck 8 13056 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range52 : checkRange pointCheck 8 13312 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range53 : checkRange pointCheck 8 13568 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range54 : checkRange pointCheck 8 13824 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range55 : checkRange pointCheck 8 14080 = true := by
  decide +kernel

end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
