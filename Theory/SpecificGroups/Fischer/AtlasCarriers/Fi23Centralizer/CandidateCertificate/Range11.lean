module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Predicates

/-!
# Fi23 point certificates: block 11

Balanced kernel reductions certify 2048 consecutive input letters. They check
the exact generator complements, word, seventh power, square and fixed image.
Source: ATLAS F23G1-p31671B0, for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
set_option Elab.async false

set_option maxRecDepth 2000 in
theorem range88 : checkRange pointCheck 8 22528 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range89 : checkRange pointCheck 8 22784 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range90 : checkRange pointCheck 8 23040 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range91 : checkRange pointCheck 8 23296 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range92 : checkRange pointCheck 8 23552 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range93 : checkRange pointCheck 8 23808 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range94 : checkRange pointCheck 8 24064 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range95 : checkRange pointCheck 8 24320 = true := by
  decide +kernel

end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
