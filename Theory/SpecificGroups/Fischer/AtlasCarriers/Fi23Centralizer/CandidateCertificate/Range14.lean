module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Predicates

/-!
# Fi23 point certificates: block 14

Balanced kernel reductions certify 2048 consecutive input letters. They check
the exact generator complements, word, seventh power, square and fixed image.
Source: ATLAS F23G1-p31671B0, for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
set_option Elab.async false

set_option maxRecDepth 2000 in
theorem range112 : checkRange pointCheck 8 28672 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range113 : checkRange pointCheck 8 28928 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range114 : checkRange pointCheck 8 29184 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range115 : checkRange pointCheck 8 29440 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range116 : checkRange pointCheck 8 29696 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range117 : checkRange pointCheck 8 29952 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range118 : checkRange pointCheck 8 30208 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range119 : checkRange pointCheck 8 30464 = true := by
  decide +kernel

end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
