module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_974848 : Path.checkChunk context decode facts instructions 974848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_975360 : Path.checkChunk context decode facts instructions 975360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_975872 : Path.checkChunk context decode facts instructions 975872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_976384 : Path.checkChunk context decode facts instructions 976384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_976896 : Path.checkChunk context decode facts instructions 976896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_977408 : Path.checkChunk context decode facts instructions 977408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_977920 : Path.checkChunk context decode facts instructions 977920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_978432 : Path.checkChunk context decode facts instructions 978432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_978944 : Path.checkChunk context decode facts instructions 978944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_979456 : Path.checkChunk context decode facts instructions 979456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_979968 : Path.checkChunk context decode facts instructions 979968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_980480 : Path.checkChunk context decode facts instructions 980480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_980992 : Path.checkChunk context decode facts instructions 980992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_981504 : Path.checkChunk context decode facts instructions 981504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_982016 : Path.checkChunk context decode facts instructions 982016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_982528 : Path.checkChunk context decode facts instructions 982528 512 = true := by
  decide +kernel

theorem sound_974848 (prior : ∀ n, n < 974848 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 983040 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h975360 := Path.chunk_sound context_valid decode facts instructions 974848 512
    prior checked_974848
  have h975872 := Path.chunk_sound context_valid decode facts instructions 975360 512
    h975360 checked_975360
  have h976384 := Path.chunk_sound context_valid decode facts instructions 975872 512
    h975872 checked_975872
  have h976896 := Path.chunk_sound context_valid decode facts instructions 976384 512
    h976384 checked_976384
  have h977408 := Path.chunk_sound context_valid decode facts instructions 976896 512
    h976896 checked_976896
  have h977920 := Path.chunk_sound context_valid decode facts instructions 977408 512
    h977408 checked_977408
  have h978432 := Path.chunk_sound context_valid decode facts instructions 977920 512
    h977920 checked_977920
  have h978944 := Path.chunk_sound context_valid decode facts instructions 978432 512
    h978432 checked_978432
  have h979456 := Path.chunk_sound context_valid decode facts instructions 978944 512
    h978944 checked_978944
  have h979968 := Path.chunk_sound context_valid decode facts instructions 979456 512
    h979456 checked_979456
  have h980480 := Path.chunk_sound context_valid decode facts instructions 979968 512
    h979968 checked_979968
  have h980992 := Path.chunk_sound context_valid decode facts instructions 980480 512
    h980480 checked_980480
  have h981504 := Path.chunk_sound context_valid decode facts instructions 980992 512
    h980992 checked_980992
  have h982016 := Path.chunk_sound context_valid decode facts instructions 981504 512
    h981504 checked_981504
  have h982528 := Path.chunk_sound context_valid decode facts instructions 982016 512
    h982016 checked_982016
  have h983040 := Path.chunk_sound context_valid decode facts instructions 982528 512
    h982528 checked_982528
  exact h983040

end Sporadic.Janko3.AmalgamPresentation.Cover
