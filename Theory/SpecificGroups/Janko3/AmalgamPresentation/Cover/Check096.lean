module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_786432 : Path.checkChunk context decode facts instructions 786432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_786944 : Path.checkChunk context decode facts instructions 786944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_787456 : Path.checkChunk context decode facts instructions 787456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_787968 : Path.checkChunk context decode facts instructions 787968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_788480 : Path.checkChunk context decode facts instructions 788480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_788992 : Path.checkChunk context decode facts instructions 788992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_789504 : Path.checkChunk context decode facts instructions 789504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_790016 : Path.checkChunk context decode facts instructions 790016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_790528 : Path.checkChunk context decode facts instructions 790528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_791040 : Path.checkChunk context decode facts instructions 791040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_791552 : Path.checkChunk context decode facts instructions 791552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_792064 : Path.checkChunk context decode facts instructions 792064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_792576 : Path.checkChunk context decode facts instructions 792576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_793088 : Path.checkChunk context decode facts instructions 793088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_793600 : Path.checkChunk context decode facts instructions 793600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_794112 : Path.checkChunk context decode facts instructions 794112 512 = true := by
  decide +kernel

theorem sound_786432 (prior : ∀ n, n < 786432 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 794624 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h786944 := Path.chunk_sound context_valid decode facts instructions 786432 512
    prior checked_786432
  have h787456 := Path.chunk_sound context_valid decode facts instructions 786944 512
    h786944 checked_786944
  have h787968 := Path.chunk_sound context_valid decode facts instructions 787456 512
    h787456 checked_787456
  have h788480 := Path.chunk_sound context_valid decode facts instructions 787968 512
    h787968 checked_787968
  have h788992 := Path.chunk_sound context_valid decode facts instructions 788480 512
    h788480 checked_788480
  have h789504 := Path.chunk_sound context_valid decode facts instructions 788992 512
    h788992 checked_788992
  have h790016 := Path.chunk_sound context_valid decode facts instructions 789504 512
    h789504 checked_789504
  have h790528 := Path.chunk_sound context_valid decode facts instructions 790016 512
    h790016 checked_790016
  have h791040 := Path.chunk_sound context_valid decode facts instructions 790528 512
    h790528 checked_790528
  have h791552 := Path.chunk_sound context_valid decode facts instructions 791040 512
    h791040 checked_791040
  have h792064 := Path.chunk_sound context_valid decode facts instructions 791552 512
    h791552 checked_791552
  have h792576 := Path.chunk_sound context_valid decode facts instructions 792064 512
    h792064 checked_792064
  have h793088 := Path.chunk_sound context_valid decode facts instructions 792576 512
    h792576 checked_792576
  have h793600 := Path.chunk_sound context_valid decode facts instructions 793088 512
    h793088 checked_793088
  have h794112 := Path.chunk_sound context_valid decode facts instructions 793600 512
    h793600 checked_793600
  have h794624 := Path.chunk_sound context_valid decode facts instructions 794112 512
    h794112 checked_794112
  exact h794624

end Sporadic.Janko3.AmalgamPresentation.Cover
