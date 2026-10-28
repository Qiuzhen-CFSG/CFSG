module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Tables

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_196608 : Scan.checkChunk context facts instructions 196608 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_197632 : Scan.checkChunk context facts instructions 197632 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_198656 : Scan.checkChunk context facts instructions 198656 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_199680 : Scan.checkChunk context facts instructions 199680 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_200704 : Scan.checkChunk context facts instructions 200704 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_201728 : Scan.checkChunk context facts instructions 201728 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_202752 : Scan.checkChunk context facts instructions 202752 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_203776 : Scan.checkChunk context facts instructions 203776 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_204800 : Scan.checkChunk context facts instructions 204800 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_205824 : Scan.checkChunk context facts instructions 205824 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_206848 : Scan.checkChunk context facts instructions 206848 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_207872 : Scan.checkChunk context facts instructions 207872 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_208896 : Scan.checkChunk context facts instructions 208896 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_209920 : Scan.checkChunk context facts instructions 209920 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_210944 : Scan.checkChunk context facts instructions 210944 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_211968 : Scan.checkChunk context facts instructions 211968 1024 = true := by
  decide +kernel

theorem sound_196608 (prior : ∀ n, n < 196608 →
    Holds M1 generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 212992 → Holds M1 generator (definitions.repr generator) (facts n) := by
  have h197632 := Scan.chunk_sound context_valid facts instructions 196608 1024
    prior checked_196608
  have h198656 := Scan.chunk_sound context_valid facts instructions 197632 1024
    h197632 checked_197632
  have h199680 := Scan.chunk_sound context_valid facts instructions 198656 1024
    h198656 checked_198656
  have h200704 := Scan.chunk_sound context_valid facts instructions 199680 1024
    h199680 checked_199680
  have h201728 := Scan.chunk_sound context_valid facts instructions 200704 1024
    h200704 checked_200704
  have h202752 := Scan.chunk_sound context_valid facts instructions 201728 1024
    h201728 checked_201728
  have h203776 := Scan.chunk_sound context_valid facts instructions 202752 1024
    h202752 checked_202752
  have h204800 := Scan.chunk_sound context_valid facts instructions 203776 1024
    h203776 checked_203776
  have h205824 := Scan.chunk_sound context_valid facts instructions 204800 1024
    h204800 checked_204800
  have h206848 := Scan.chunk_sound context_valid facts instructions 205824 1024
    h205824 checked_205824
  have h207872 := Scan.chunk_sound context_valid facts instructions 206848 1024
    h206848 checked_206848
  have h208896 := Scan.chunk_sound context_valid facts instructions 207872 1024
    h207872 checked_207872
  have h209920 := Scan.chunk_sound context_valid facts instructions 208896 1024
    h208896 checked_208896
  have h210944 := Scan.chunk_sound context_valid facts instructions 209920 1024
    h209920 checked_209920
  have h211968 := Scan.chunk_sound context_valid facts instructions 210944 1024
    h210944 checked_210944
  have h212992 := Scan.chunk_sound context_valid facts instructions 211968 1024
    h211968 checked_211968
  exact h212992

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
