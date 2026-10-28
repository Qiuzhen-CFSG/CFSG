module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Tables

/-! Centralizer-coset certificate for the thirteen ATLAS HS relators.
Untrusted data generated from the retained trace; all deduction checks use
Lean's kernel and the actual abstract relations. See `source/README.md`. -/

public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_196608 : Scan.checkChunk context facts instructions 196608 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_197120 : Scan.checkChunk context facts instructions 197120 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_197632 : Scan.checkChunk context facts instructions 197632 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_198144 : Scan.checkChunk context facts instructions 198144 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_198656 : Scan.checkChunk context facts instructions 198656 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_199168 : Scan.checkChunk context facts instructions 199168 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_199680 : Scan.checkChunk context facts instructions 199680 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_200192 : Scan.checkChunk context facts instructions 200192 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_200704 : Scan.checkChunk context facts instructions 200704 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_201216 : Scan.checkChunk context facts instructions 201216 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_201728 : Scan.checkChunk context facts instructions 201728 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_202240 : Scan.checkChunk context facts instructions 202240 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_202752 : Scan.checkChunk context facts instructions 202752 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_203264 : Scan.checkChunk context facts instructions 203264 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_203776 : Scan.checkChunk context facts instructions 203776 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_204288 : Scan.checkChunk context facts instructions 204288 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_204800 : Scan.checkChunk context facts instructions 204800 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_205312 : Scan.checkChunk context facts instructions 205312 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_205824 : Scan.checkChunk context facts instructions 205824 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_206336 : Scan.checkChunk context facts instructions 206336 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_206848 : Scan.checkChunk context facts instructions 206848 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_207360 : Scan.checkChunk context facts instructions 207360 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_207872 : Scan.checkChunk context facts instructions 207872 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_208384 : Scan.checkChunk context facts instructions 208384 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_208896 : Scan.checkChunk context facts instructions 208896 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_209408 : Scan.checkChunk context facts instructions 209408 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_209920 : Scan.checkChunk context facts instructions 209920 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_210432 : Scan.checkChunk context facts instructions 210432 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_210944 : Scan.checkChunk context facts instructions 210944 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_211456 : Scan.checkChunk context facts instructions 211456 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_211968 : Scan.checkChunk context facts instructions 211968 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_212480 : Scan.checkChunk context facts instructions 212480 512 = true := by
  decide +kernel

theorem all_hold_212992 (prior : ∀ n, n < 196608 → Holds centralizer certGenerator (definitions.repr certGenerator) (facts n)) : ∀ n, n < 212992 →
    Holds centralizer certGenerator (definitions.repr certGenerator) (facts n) := by
  have h197120 := Scan.chunk_sound context_valid facts instructions 196608 512
    prior checked_196608
  have h197632 := Scan.chunk_sound context_valid facts instructions 197120 512
    h197120 checked_197120
  have h198144 := Scan.chunk_sound context_valid facts instructions 197632 512
    h197632 checked_197632
  have h198656 := Scan.chunk_sound context_valid facts instructions 198144 512
    h198144 checked_198144
  have h199168 := Scan.chunk_sound context_valid facts instructions 198656 512
    h198656 checked_198656
  have h199680 := Scan.chunk_sound context_valid facts instructions 199168 512
    h199168 checked_199168
  have h200192 := Scan.chunk_sound context_valid facts instructions 199680 512
    h199680 checked_199680
  have h200704 := Scan.chunk_sound context_valid facts instructions 200192 512
    h200192 checked_200192
  have h201216 := Scan.chunk_sound context_valid facts instructions 200704 512
    h200704 checked_200704
  have h201728 := Scan.chunk_sound context_valid facts instructions 201216 512
    h201216 checked_201216
  have h202240 := Scan.chunk_sound context_valid facts instructions 201728 512
    h201728 checked_201728
  have h202752 := Scan.chunk_sound context_valid facts instructions 202240 512
    h202240 checked_202240
  have h203264 := Scan.chunk_sound context_valid facts instructions 202752 512
    h202752 checked_202752
  have h203776 := Scan.chunk_sound context_valid facts instructions 203264 512
    h203264 checked_203264
  have h204288 := Scan.chunk_sound context_valid facts instructions 203776 512
    h203776 checked_203776
  have h204800 := Scan.chunk_sound context_valid facts instructions 204288 512
    h204288 checked_204288
  have h205312 := Scan.chunk_sound context_valid facts instructions 204800 512
    h204800 checked_204800
  have h205824 := Scan.chunk_sound context_valid facts instructions 205312 512
    h205312 checked_205312
  have h206336 := Scan.chunk_sound context_valid facts instructions 205824 512
    h205824 checked_205824
  have h206848 := Scan.chunk_sound context_valid facts instructions 206336 512
    h206336 checked_206336
  have h207360 := Scan.chunk_sound context_valid facts instructions 206848 512
    h206848 checked_206848
  have h207872 := Scan.chunk_sound context_valid facts instructions 207360 512
    h207360 checked_207360
  have h208384 := Scan.chunk_sound context_valid facts instructions 207872 512
    h207872 checked_207872
  have h208896 := Scan.chunk_sound context_valid facts instructions 208384 512
    h208384 checked_208384
  have h209408 := Scan.chunk_sound context_valid facts instructions 208896 512
    h208896 checked_208896
  have h209920 := Scan.chunk_sound context_valid facts instructions 209408 512
    h209408 checked_209408
  have h210432 := Scan.chunk_sound context_valid facts instructions 209920 512
    h209920 checked_209920
  have h210944 := Scan.chunk_sound context_valid facts instructions 210432 512
    h210432 checked_210432
  have h211456 := Scan.chunk_sound context_valid facts instructions 210944 512
    h210944 checked_210944
  have h211968 := Scan.chunk_sound context_valid facts instructions 211456 512
    h211456 checked_211456
  have h212480 := Scan.chunk_sound context_valid facts instructions 211968 512
    h211968 checked_211968
  have h212992 := Scan.chunk_sound context_valid facts instructions 212480 512
    h212480 checked_212480
  exact h212992

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
