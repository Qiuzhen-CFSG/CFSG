module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_950272 : Path.checkChunk context decode facts instructions 950272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_950784 : Path.checkChunk context decode facts instructions 950784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_951296 : Path.checkChunk context decode facts instructions 951296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_951808 : Path.checkChunk context decode facts instructions 951808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_952320 : Path.checkChunk context decode facts instructions 952320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_952832 : Path.checkChunk context decode facts instructions 952832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_953344 : Path.checkChunk context decode facts instructions 953344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_953856 : Path.checkChunk context decode facts instructions 953856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_954368 : Path.checkChunk context decode facts instructions 954368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_954880 : Path.checkChunk context decode facts instructions 954880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_955392 : Path.checkChunk context decode facts instructions 955392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_955904 : Path.checkChunk context decode facts instructions 955904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_956416 : Path.checkChunk context decode facts instructions 956416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_956928 : Path.checkChunk context decode facts instructions 956928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_957440 : Path.checkChunk context decode facts instructions 957440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_957952 : Path.checkChunk context decode facts instructions 957952 512 = true := by
  decide +kernel

theorem sound_950272 (prior : ∀ n, n < 950272 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 958464 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h950784 := Path.chunk_sound context_valid decode facts instructions 950272 512
    prior checked_950272
  have h951296 := Path.chunk_sound context_valid decode facts instructions 950784 512
    h950784 checked_950784
  have h951808 := Path.chunk_sound context_valid decode facts instructions 951296 512
    h951296 checked_951296
  have h952320 := Path.chunk_sound context_valid decode facts instructions 951808 512
    h951808 checked_951808
  have h952832 := Path.chunk_sound context_valid decode facts instructions 952320 512
    h952320 checked_952320
  have h953344 := Path.chunk_sound context_valid decode facts instructions 952832 512
    h952832 checked_952832
  have h953856 := Path.chunk_sound context_valid decode facts instructions 953344 512
    h953344 checked_953344
  have h954368 := Path.chunk_sound context_valid decode facts instructions 953856 512
    h953856 checked_953856
  have h954880 := Path.chunk_sound context_valid decode facts instructions 954368 512
    h954368 checked_954368
  have h955392 := Path.chunk_sound context_valid decode facts instructions 954880 512
    h954880 checked_954880
  have h955904 := Path.chunk_sound context_valid decode facts instructions 955392 512
    h955392 checked_955392
  have h956416 := Path.chunk_sound context_valid decode facts instructions 955904 512
    h955904 checked_955904
  have h956928 := Path.chunk_sound context_valid decode facts instructions 956416 512
    h956416 checked_956416
  have h957440 := Path.chunk_sound context_valid decode facts instructions 956928 512
    h956928 checked_956928
  have h957952 := Path.chunk_sound context_valid decode facts instructions 957440 512
    h957440 checked_957440
  have h958464 := Path.chunk_sound context_valid decode facts instructions 957952 512
    h957952 checked_957952
  exact h958464

end Sporadic.Janko3.AmalgamPresentation.Cover
