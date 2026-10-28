module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Predicates

/-!
# Fi23 point certificates: block 3

Balanced kernel reductions certify 2048 consecutive input letters. They check
the exact generator complements, word, seventh power, square and fixed image.
Source: ATLAS F23G1-p31671B0, for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
set_option Elab.async false

set_option maxRecDepth 2000 in
theorem range24 : checkRange pointCheck 8 6144 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range25 : checkRange pointCheck 8 6400 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range26 : checkRange pointCheck 8 6656 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range27 : checkRange pointCheck 8 6912 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range28 : checkRange pointCheck 8 7168 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range29 : checkRange pointCheck 8 7424 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range30 : checkRange pointCheck 8 7680 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
theorem range31 : checkRange pointCheck 8 7936 = true := by
  decide +kernel

end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
