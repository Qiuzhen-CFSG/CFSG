module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Predicates

/-!
# Fi23 point certificates: block 5

Balanced kernel reductions certify 2048 consecutive input letters. They check
the exact generator complements, word, seventh power, square and fixed image.
Source: ATLAS F23G1-p31671B0, for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
set_option Elab.async false

set_option maxRecDepth 2000 in
theorem range40 : checkRange pointCheck 8 10240 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range41 : checkRange pointCheck 8 10496 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range42 : checkRange pointCheck 8 10752 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range43 : checkRange pointCheck 8 11008 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range44 : checkRange pointCheck 8 11264 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range45 : checkRange pointCheck 8 11520 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range46 : checkRange pointCheck 8 11776 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range47 : checkRange pointCheck 8 12032 = true := by
  decide +kernel

end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
