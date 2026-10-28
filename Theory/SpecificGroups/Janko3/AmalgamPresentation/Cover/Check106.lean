module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_868352 : Path.checkChunk context decode facts instructions 868352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_868864 : Path.checkChunk context decode facts instructions 868864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_869376 : Path.checkChunk context decode facts instructions 869376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_869888 : Path.checkChunk context decode facts instructions 869888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_870400 : Path.checkChunk context decode facts instructions 870400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_870912 : Path.checkChunk context decode facts instructions 870912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_871424 : Path.checkChunk context decode facts instructions 871424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_871936 : Path.checkChunk context decode facts instructions 871936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_872448 : Path.checkChunk context decode facts instructions 872448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_872960 : Path.checkChunk context decode facts instructions 872960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_873472 : Path.checkChunk context decode facts instructions 873472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_873984 : Path.checkChunk context decode facts instructions 873984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_874496 : Path.checkChunk context decode facts instructions 874496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_875008 : Path.checkChunk context decode facts instructions 875008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_875520 : Path.checkChunk context decode facts instructions 875520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_876032 : Path.checkChunk context decode facts instructions 876032 512 = true := by
  decide +kernel

theorem sound_868352 (prior : ∀ n, n < 868352 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 876544 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h868864 := Path.chunk_sound context_valid decode facts instructions 868352 512
    prior checked_868352
  have h869376 := Path.chunk_sound context_valid decode facts instructions 868864 512
    h868864 checked_868864
  have h869888 := Path.chunk_sound context_valid decode facts instructions 869376 512
    h869376 checked_869376
  have h870400 := Path.chunk_sound context_valid decode facts instructions 869888 512
    h869888 checked_869888
  have h870912 := Path.chunk_sound context_valid decode facts instructions 870400 512
    h870400 checked_870400
  have h871424 := Path.chunk_sound context_valid decode facts instructions 870912 512
    h870912 checked_870912
  have h871936 := Path.chunk_sound context_valid decode facts instructions 871424 512
    h871424 checked_871424
  have h872448 := Path.chunk_sound context_valid decode facts instructions 871936 512
    h871936 checked_871936
  have h872960 := Path.chunk_sound context_valid decode facts instructions 872448 512
    h872448 checked_872448
  have h873472 := Path.chunk_sound context_valid decode facts instructions 872960 512
    h872960 checked_872960
  have h873984 := Path.chunk_sound context_valid decode facts instructions 873472 512
    h873472 checked_873472
  have h874496 := Path.chunk_sound context_valid decode facts instructions 873984 512
    h873984 checked_873984
  have h875008 := Path.chunk_sound context_valid decode facts instructions 874496 512
    h874496 checked_874496
  have h875520 := Path.chunk_sound context_valid decode facts instructions 875008 512
    h875008 checked_875008
  have h876032 := Path.chunk_sound context_valid decode facts instructions 875520 512
    h875520 checked_875520
  have h876544 := Path.chunk_sound context_valid decode facts instructions 876032 512
    h876032 checked_876032
  exact h876544

end Sporadic.Janko3.AmalgamPresentation.Cover
