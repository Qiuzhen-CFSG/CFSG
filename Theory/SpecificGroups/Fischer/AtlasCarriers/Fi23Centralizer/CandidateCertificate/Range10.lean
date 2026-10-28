module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Predicates

/-!
# Fi23 point certificates: block 10

Balanced kernel reductions certify 2048 consecutive input letters. They check
the exact generator complements, word, seventh power, square and fixed image.
Source: ATLAS F23G1-p31671B0, for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
set_option Elab.async false

set_option maxRecDepth 2000 in
theorem range80 : checkRange pointCheck 8 20480 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range81 : checkRange pointCheck 8 20736 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range82 : checkRange pointCheck 8 20992 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range83 : checkRange pointCheck 8 21248 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range84 : checkRange pointCheck 8 21504 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range85 : checkRange pointCheck 8 21760 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range86 : checkRange pointCheck 8 22016 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range87 : checkRange pointCheck 8 22272 = true := by
  decide +kernel

end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
