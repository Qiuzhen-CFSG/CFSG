module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Predicates

/-!
# Fi23 point certificates: block 0

Balanced kernel reductions certify 2048 consecutive input letters. They check
the exact generator complements, word, seventh power, square and fixed image.
Source: ATLAS F23G1-p31671B0, for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
set_option Elab.async false

set_option maxRecDepth 2000 in
theorem range0 : checkRange pointCheck 8 0 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range1 : checkRange pointCheck 8 256 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range2 : checkRange pointCheck 8 512 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range3 : checkRange pointCheck 8 768 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range4 : checkRange pointCheck 8 1024 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range5 : checkRange pointCheck 8 1280 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range6 : checkRange pointCheck 8 1536 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range7 : checkRange pointCheck 8 1792 = true := by
  decide +kernel

end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
