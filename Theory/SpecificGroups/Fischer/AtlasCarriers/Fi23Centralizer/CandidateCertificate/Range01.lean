module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Predicates

/-!
# Fi23 point certificates: block 1

Balanced kernel reductions certify 2048 consecutive input letters. They check
the exact generator complements, word, seventh power, square and fixed image.
Source: ATLAS F23G1-p31671B0, for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
set_option Elab.async false

set_option maxRecDepth 2000 in
theorem range8 : checkRange pointCheck 8 2048 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range9 : checkRange pointCheck 8 2304 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range10 : checkRange pointCheck 8 2560 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range11 : checkRange pointCheck 8 2816 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range12 : checkRange pointCheck 8 3072 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range13 : checkRange pointCheck 8 3328 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range14 : checkRange pointCheck 8 3584 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range15 : checkRange pointCheck 8 3840 = true := by
  decide +kernel

end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
