module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_57344 : Path.checkChunk context decode facts instructions 57344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_57856 : Path.checkChunk context decode facts instructions 57856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_58368 : Path.checkChunk context decode facts instructions 58368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_58880 : Path.checkChunk context decode facts instructions 58880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_59392 : Path.checkChunk context decode facts instructions 59392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_59904 : Path.checkChunk context decode facts instructions 59904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_60416 : Path.checkChunk context decode facts instructions 60416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_60928 : Path.checkChunk context decode facts instructions 60928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_61440 : Path.checkChunk context decode facts instructions 61440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_61952 : Path.checkChunk context decode facts instructions 61952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_62464 : Path.checkChunk context decode facts instructions 62464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_62976 : Path.checkChunk context decode facts instructions 62976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_63488 : Path.checkChunk context decode facts instructions 63488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_64000 : Path.checkChunk context decode facts instructions 64000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_64512 : Path.checkChunk context decode facts instructions 64512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_65024 : Path.checkChunk context decode facts instructions 65024 512 = true := by
  decide +kernel

theorem sound_57344 (prior : ∀ n, n < 57344 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 65536 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h57856 := Path.chunk_sound context_valid decode facts instructions 57344 512
    prior checked_57344
  have h58368 := Path.chunk_sound context_valid decode facts instructions 57856 512
    h57856 checked_57856
  have h58880 := Path.chunk_sound context_valid decode facts instructions 58368 512
    h58368 checked_58368
  have h59392 := Path.chunk_sound context_valid decode facts instructions 58880 512
    h58880 checked_58880
  have h59904 := Path.chunk_sound context_valid decode facts instructions 59392 512
    h59392 checked_59392
  have h60416 := Path.chunk_sound context_valid decode facts instructions 59904 512
    h59904 checked_59904
  have h60928 := Path.chunk_sound context_valid decode facts instructions 60416 512
    h60416 checked_60416
  have h61440 := Path.chunk_sound context_valid decode facts instructions 60928 512
    h60928 checked_60928
  have h61952 := Path.chunk_sound context_valid decode facts instructions 61440 512
    h61440 checked_61440
  have h62464 := Path.chunk_sound context_valid decode facts instructions 61952 512
    h61952 checked_61952
  have h62976 := Path.chunk_sound context_valid decode facts instructions 62464 512
    h62464 checked_62464
  have h63488 := Path.chunk_sound context_valid decode facts instructions 62976 512
    h62976 checked_62976
  have h64000 := Path.chunk_sound context_valid decode facts instructions 63488 512
    h63488 checked_63488
  have h64512 := Path.chunk_sound context_valid decode facts instructions 64000 512
    h64000 checked_64000
  have h65024 := Path.chunk_sound context_valid decode facts instructions 64512 512
    h64512 checked_64512
  have h65536 := Path.chunk_sound context_valid decode facts instructions 65024 512
    h65024 checked_65024
  exact h65536

end Sporadic.Janko3.AmalgamPresentation.Cover
