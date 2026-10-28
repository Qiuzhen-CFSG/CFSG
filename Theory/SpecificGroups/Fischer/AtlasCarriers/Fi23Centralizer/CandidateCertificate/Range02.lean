module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Predicates

/-!
# Fi23 point certificates: block 2

Balanced kernel reductions certify 2048 consecutive input letters. They check
the exact generator complements, word, seventh power, square and fixed image.
Source: ATLAS F23G1-p31671B0, for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
set_option Elab.async false

set_option maxRecDepth 2000 in
theorem range16 : checkRange pointCheck 8 4096 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range17 : checkRange pointCheck 8 4352 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range18 : checkRange pointCheck 8 4608 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range19 : checkRange pointCheck 8 4864 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range20 : checkRange pointCheck 8 5120 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range21 : checkRange pointCheck 8 5376 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range22 : checkRange pointCheck 8 5632 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range23 : checkRange pointCheck 8 5888 = true := by
  decide +kernel

end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
