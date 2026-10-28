module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Predicates

/-!
# Fi23 point certificates: block 13

Balanced kernel reductions certify 2048 consecutive input letters. They check
the exact generator complements, word, seventh power, square and fixed image.
Source: ATLAS F23G1-p31671B0, for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
set_option Elab.async false

set_option maxRecDepth 2000 in
theorem range104 : checkRange pointCheck 8 26624 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range105 : checkRange pointCheck 8 26880 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range106 : checkRange pointCheck 8 27136 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range107 : checkRange pointCheck 8 27392 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range108 : checkRange pointCheck 8 27648 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range109 : checkRange pointCheck 8 27904 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range110 : checkRange pointCheck 8 28160 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range111 : checkRange pointCheck 8 28416 = true := by
  decide +kernel

end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
