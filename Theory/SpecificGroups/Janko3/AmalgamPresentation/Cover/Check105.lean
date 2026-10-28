module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_860160 : Path.checkChunk context decode facts instructions 860160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_860672 : Path.checkChunk context decode facts instructions 860672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_861184 : Path.checkChunk context decode facts instructions 861184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_861696 : Path.checkChunk context decode facts instructions 861696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_862208 : Path.checkChunk context decode facts instructions 862208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_862720 : Path.checkChunk context decode facts instructions 862720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_863232 : Path.checkChunk context decode facts instructions 863232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_863744 : Path.checkChunk context decode facts instructions 863744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_864256 : Path.checkChunk context decode facts instructions 864256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_864768 : Path.checkChunk context decode facts instructions 864768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_865280 : Path.checkChunk context decode facts instructions 865280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_865792 : Path.checkChunk context decode facts instructions 865792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_866304 : Path.checkChunk context decode facts instructions 866304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_866816 : Path.checkChunk context decode facts instructions 866816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_867328 : Path.checkChunk context decode facts instructions 867328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_867840 : Path.checkChunk context decode facts instructions 867840 512 = true := by
  decide +kernel

theorem sound_860160 (prior : ∀ n, n < 860160 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 868352 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h860672 := Path.chunk_sound context_valid decode facts instructions 860160 512
    prior checked_860160
  have h861184 := Path.chunk_sound context_valid decode facts instructions 860672 512
    h860672 checked_860672
  have h861696 := Path.chunk_sound context_valid decode facts instructions 861184 512
    h861184 checked_861184
  have h862208 := Path.chunk_sound context_valid decode facts instructions 861696 512
    h861696 checked_861696
  have h862720 := Path.chunk_sound context_valid decode facts instructions 862208 512
    h862208 checked_862208
  have h863232 := Path.chunk_sound context_valid decode facts instructions 862720 512
    h862720 checked_862720
  have h863744 := Path.chunk_sound context_valid decode facts instructions 863232 512
    h863232 checked_863232
  have h864256 := Path.chunk_sound context_valid decode facts instructions 863744 512
    h863744 checked_863744
  have h864768 := Path.chunk_sound context_valid decode facts instructions 864256 512
    h864256 checked_864256
  have h865280 := Path.chunk_sound context_valid decode facts instructions 864768 512
    h864768 checked_864768
  have h865792 := Path.chunk_sound context_valid decode facts instructions 865280 512
    h865280 checked_865280
  have h866304 := Path.chunk_sound context_valid decode facts instructions 865792 512
    h865792 checked_865792
  have h866816 := Path.chunk_sound context_valid decode facts instructions 866304 512
    h866304 checked_866304
  have h867328 := Path.chunk_sound context_valid decode facts instructions 866816 512
    h866816 checked_866816
  have h867840 := Path.chunk_sound context_valid decode facts instructions 867328 512
    h867328 checked_867328
  have h868352 := Path.chunk_sound context_valid decode facts instructions 867840 512
    h867840 checked_867840
  exact h868352

end Sporadic.Janko3.AmalgamPresentation.Cover
