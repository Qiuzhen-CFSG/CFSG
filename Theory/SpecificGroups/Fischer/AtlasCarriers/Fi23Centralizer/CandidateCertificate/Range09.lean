module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Predicates

/-!
# Fi23 point certificates: block 9

Balanced kernel reductions certify 2048 consecutive input letters. They check
the exact generator complements, word, seventh power, square and fixed image.
Source: ATLAS F23G1-p31671B0, for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
set_option Elab.async false

set_option maxRecDepth 2000 in
theorem range72 : checkRange pointCheck 8 18432 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range73 : checkRange pointCheck 8 18688 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range74 : checkRange pointCheck 8 18944 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range75 : checkRange pointCheck 8 19200 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range76 : checkRange pointCheck 8 19456 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range77 : checkRange pointCheck 8 19712 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range78 : checkRange pointCheck 8 19968 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range79 : checkRange pointCheck 8 20224 = true := by
  decide +kernel

end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
