module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Predicates

/-!
# Fi23 point certificates: block 8

Balanced kernel reductions certify 2048 consecutive input letters. They check
the exact generator complements, word, seventh power, square and fixed image.
Source: ATLAS F23G1-p31671B0, for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
set_option Elab.async false

set_option maxRecDepth 2000 in
theorem range64 : checkRange pointCheck 8 16384 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range65 : checkRange pointCheck 8 16640 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range66 : checkRange pointCheck 8 16896 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range67 : checkRange pointCheck 8 17152 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range68 : checkRange pointCheck 8 17408 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range69 : checkRange pointCheck 8 17664 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range70 : checkRange pointCheck 8 17920 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range71 : checkRange pointCheck 8 18176 = true := by
  decide +kernel

end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
