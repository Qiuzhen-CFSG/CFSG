module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Predicates

/-!
# Fi23 point certificates: block 15

Balanced kernel reductions certify 2048 consecutive input letters. They check
the exact generator complements, word, seventh power, square and fixed image.
Source: ATLAS F23G1-p31671B0, for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
set_option Elab.async false

set_option maxRecDepth 2000 in
theorem range120 : checkRange pointCheck 8 30720 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range121 : checkRange pointCheck 8 30976 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range122 : checkRange pointCheck 8 31232 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range123 : checkRange pointCheck 8 31488 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range124 : checkRange pointCheck 8 31744 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range125 : checkRange pointCheck 8 32000 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range126 : checkRange pointCheck 8 32256 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range127 : checkRange pointCheck 8 32512 = true := by
  decide +kernel

end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
