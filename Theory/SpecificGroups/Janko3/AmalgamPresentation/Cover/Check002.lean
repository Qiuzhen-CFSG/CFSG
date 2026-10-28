module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_16384 : Path.checkChunk context decode facts instructions 16384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_16896 : Path.checkChunk context decode facts instructions 16896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_17408 : Path.checkChunk context decode facts instructions 17408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_17920 : Path.checkChunk context decode facts instructions 17920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_18432 : Path.checkChunk context decode facts instructions 18432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_18944 : Path.checkChunk context decode facts instructions 18944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_19456 : Path.checkChunk context decode facts instructions 19456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_19968 : Path.checkChunk context decode facts instructions 19968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_20480 : Path.checkChunk context decode facts instructions 20480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_20992 : Path.checkChunk context decode facts instructions 20992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_21504 : Path.checkChunk context decode facts instructions 21504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_22016 : Path.checkChunk context decode facts instructions 22016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_22528 : Path.checkChunk context decode facts instructions 22528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_23040 : Path.checkChunk context decode facts instructions 23040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_23552 : Path.checkChunk context decode facts instructions 23552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_24064 : Path.checkChunk context decode facts instructions 24064 512 = true := by
  decide +kernel

theorem sound_16384 (prior : ∀ n, n < 16384 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 24576 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h16896 := Path.chunk_sound context_valid decode facts instructions 16384 512
    prior checked_16384
  have h17408 := Path.chunk_sound context_valid decode facts instructions 16896 512
    h16896 checked_16896
  have h17920 := Path.chunk_sound context_valid decode facts instructions 17408 512
    h17408 checked_17408
  have h18432 := Path.chunk_sound context_valid decode facts instructions 17920 512
    h17920 checked_17920
  have h18944 := Path.chunk_sound context_valid decode facts instructions 18432 512
    h18432 checked_18432
  have h19456 := Path.chunk_sound context_valid decode facts instructions 18944 512
    h18944 checked_18944
  have h19968 := Path.chunk_sound context_valid decode facts instructions 19456 512
    h19456 checked_19456
  have h20480 := Path.chunk_sound context_valid decode facts instructions 19968 512
    h19968 checked_19968
  have h20992 := Path.chunk_sound context_valid decode facts instructions 20480 512
    h20480 checked_20480
  have h21504 := Path.chunk_sound context_valid decode facts instructions 20992 512
    h20992 checked_20992
  have h22016 := Path.chunk_sound context_valid decode facts instructions 21504 512
    h21504 checked_21504
  have h22528 := Path.chunk_sound context_valid decode facts instructions 22016 512
    h22016 checked_22016
  have h23040 := Path.chunk_sound context_valid decode facts instructions 22528 512
    h22528 checked_22528
  have h23552 := Path.chunk_sound context_valid decode facts instructions 23040 512
    h23040 checked_23040
  have h24064 := Path.chunk_sound context_valid decode facts instructions 23552 512
    h23552 checked_23552
  have h24576 := Path.chunk_sound context_valid decode facts instructions 24064 512
    h24064 checked_24064
  exact h24576

end Sporadic.Janko3.AmalgamPresentation.Cover
