module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Predicates

/-!
# Fi23 point certificates: block 4

Balanced kernel reductions certify 2048 consecutive input letters. They check
the exact generator complements, word, seventh power, square and fixed image.
Source: ATLAS F23G1-p31671B0, for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
set_option Elab.async false

set_option maxRecDepth 2000 in
theorem range32 : checkRange pointCheck 8 8192 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range33 : checkRange pointCheck 8 8448 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range34 : checkRange pointCheck 8 8704 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range35 : checkRange pointCheck 8 8960 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range36 : checkRange pointCheck 8 9216 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range37 : checkRange pointCheck 8 9472 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range38 : checkRange pointCheck 8 9728 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range39 : checkRange pointCheck 8 9984 = true := by
  decide +kernel

end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
