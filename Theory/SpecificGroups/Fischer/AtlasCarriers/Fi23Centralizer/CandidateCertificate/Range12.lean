module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Predicates

/-!
# Fi23 point certificates: block 12

Balanced kernel reductions certify 2048 consecutive input letters. They check
the exact generator complements, word, seventh power, square and fixed image.
Source: ATLAS F23G1-p31671B0, for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
set_option Elab.async false

set_option maxRecDepth 2000 in
theorem range96 : checkRange pointCheck 8 24576 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range97 : checkRange pointCheck 8 24832 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range98 : checkRange pointCheck 8 25088 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range99 : checkRange pointCheck 8 25344 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range100 : checkRange pointCheck 8 25600 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range101 : checkRange pointCheck 8 25856 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range102 : checkRange pointCheck 8 26112 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range103 : checkRange pointCheck 8 26368 = true := by
  decide +kernel

end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
