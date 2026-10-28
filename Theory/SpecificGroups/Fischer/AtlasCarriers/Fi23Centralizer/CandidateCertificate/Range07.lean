module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Predicates

/-!
# Fi23 point certificates: block 7

Balanced kernel reductions certify 2048 consecutive input letters. They check
the exact generator complements, word, seventh power, square and fixed image.
Source: ATLAS F23G1-p31671B0, for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
set_option Elab.async false

set_option maxRecDepth 2000 in
theorem range56 : checkRange pointCheck 8 14336 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range57 : checkRange pointCheck 8 14592 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range58 : checkRange pointCheck 8 14848 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range59 : checkRange pointCheck 8 15104 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range60 : checkRange pointCheck 8 15360 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range61 : checkRange pointCheck 8 15616 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range62 : checkRange pointCheck 8 15872 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range63 : checkRange pointCheck 8 16128 = true := by
  decide +kernel

end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
