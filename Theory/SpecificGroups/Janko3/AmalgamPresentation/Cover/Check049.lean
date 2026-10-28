module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_401408 : Path.checkChunk context decode facts instructions 401408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_401920 : Path.checkChunk context decode facts instructions 401920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_402432 : Path.checkChunk context decode facts instructions 402432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_402944 : Path.checkChunk context decode facts instructions 402944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_403456 : Path.checkChunk context decode facts instructions 403456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_403968 : Path.checkChunk context decode facts instructions 403968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_404480 : Path.checkChunk context decode facts instructions 404480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_404992 : Path.checkChunk context decode facts instructions 404992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_405504 : Path.checkChunk context decode facts instructions 405504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_406016 : Path.checkChunk context decode facts instructions 406016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_406528 : Path.checkChunk context decode facts instructions 406528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_407040 : Path.checkChunk context decode facts instructions 407040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_407552 : Path.checkChunk context decode facts instructions 407552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_408064 : Path.checkChunk context decode facts instructions 408064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_408576 : Path.checkChunk context decode facts instructions 408576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_409088 : Path.checkChunk context decode facts instructions 409088 512 = true := by
  decide +kernel

theorem sound_401408 (prior : ∀ n, n < 401408 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 409600 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h401920 := Path.chunk_sound context_valid decode facts instructions 401408 512
    prior checked_401408
  have h402432 := Path.chunk_sound context_valid decode facts instructions 401920 512
    h401920 checked_401920
  have h402944 := Path.chunk_sound context_valid decode facts instructions 402432 512
    h402432 checked_402432
  have h403456 := Path.chunk_sound context_valid decode facts instructions 402944 512
    h402944 checked_402944
  have h403968 := Path.chunk_sound context_valid decode facts instructions 403456 512
    h403456 checked_403456
  have h404480 := Path.chunk_sound context_valid decode facts instructions 403968 512
    h403968 checked_403968
  have h404992 := Path.chunk_sound context_valid decode facts instructions 404480 512
    h404480 checked_404480
  have h405504 := Path.chunk_sound context_valid decode facts instructions 404992 512
    h404992 checked_404992
  have h406016 := Path.chunk_sound context_valid decode facts instructions 405504 512
    h405504 checked_405504
  have h406528 := Path.chunk_sound context_valid decode facts instructions 406016 512
    h406016 checked_406016
  have h407040 := Path.chunk_sound context_valid decode facts instructions 406528 512
    h406528 checked_406528
  have h407552 := Path.chunk_sound context_valid decode facts instructions 407040 512
    h407040 checked_407040
  have h408064 := Path.chunk_sound context_valid decode facts instructions 407552 512
    h407552 checked_407552
  have h408576 := Path.chunk_sound context_valid decode facts instructions 408064 512
    h408064 checked_408064
  have h409088 := Path.chunk_sound context_valid decode facts instructions 408576 512
    h408576 checked_408576
  have h409600 := Path.chunk_sound context_valid decode facts instructions 409088 512
    h409088 checked_409088
  exact h409600

end Sporadic.Janko3.AmalgamPresentation.Cover
