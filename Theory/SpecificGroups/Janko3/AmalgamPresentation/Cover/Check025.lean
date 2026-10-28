module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_204800 : Path.checkChunk context decode facts instructions 204800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_205312 : Path.checkChunk context decode facts instructions 205312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_205824 : Path.checkChunk context decode facts instructions 205824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_206336 : Path.checkChunk context decode facts instructions 206336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_206848 : Path.checkChunk context decode facts instructions 206848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_207360 : Path.checkChunk context decode facts instructions 207360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_207872 : Path.checkChunk context decode facts instructions 207872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_208384 : Path.checkChunk context decode facts instructions 208384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_208896 : Path.checkChunk context decode facts instructions 208896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_209408 : Path.checkChunk context decode facts instructions 209408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_209920 : Path.checkChunk context decode facts instructions 209920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_210432 : Path.checkChunk context decode facts instructions 210432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_210944 : Path.checkChunk context decode facts instructions 210944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_211456 : Path.checkChunk context decode facts instructions 211456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_211968 : Path.checkChunk context decode facts instructions 211968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_212480 : Path.checkChunk context decode facts instructions 212480 512 = true := by
  decide +kernel

theorem sound_204800 (prior : ∀ n, n < 204800 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 212992 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h205312 := Path.chunk_sound context_valid decode facts instructions 204800 512
    prior checked_204800
  have h205824 := Path.chunk_sound context_valid decode facts instructions 205312 512
    h205312 checked_205312
  have h206336 := Path.chunk_sound context_valid decode facts instructions 205824 512
    h205824 checked_205824
  have h206848 := Path.chunk_sound context_valid decode facts instructions 206336 512
    h206336 checked_206336
  have h207360 := Path.chunk_sound context_valid decode facts instructions 206848 512
    h206848 checked_206848
  have h207872 := Path.chunk_sound context_valid decode facts instructions 207360 512
    h207360 checked_207360
  have h208384 := Path.chunk_sound context_valid decode facts instructions 207872 512
    h207872 checked_207872
  have h208896 := Path.chunk_sound context_valid decode facts instructions 208384 512
    h208384 checked_208384
  have h209408 := Path.chunk_sound context_valid decode facts instructions 208896 512
    h208896 checked_208896
  have h209920 := Path.chunk_sound context_valid decode facts instructions 209408 512
    h209408 checked_209408
  have h210432 := Path.chunk_sound context_valid decode facts instructions 209920 512
    h209920 checked_209920
  have h210944 := Path.chunk_sound context_valid decode facts instructions 210432 512
    h210432 checked_210432
  have h211456 := Path.chunk_sound context_valid decode facts instructions 210944 512
    h210944 checked_210944
  have h211968 := Path.chunk_sound context_valid decode facts instructions 211456 512
    h211456 checked_211456
  have h212480 := Path.chunk_sound context_valid decode facts instructions 211968 512
    h211968 checked_211968
  have h212992 := Path.chunk_sound context_valid decode facts instructions 212480 512
    h212480 checked_212480
  exact h212992

end Sporadic.Janko3.AmalgamPresentation.Cover
