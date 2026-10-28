module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_32768 : Path.checkChunk context decode facts instructions 32768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_33280 : Path.checkChunk context decode facts instructions 33280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_33792 : Path.checkChunk context decode facts instructions 33792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_34304 : Path.checkChunk context decode facts instructions 34304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_34816 : Path.checkChunk context decode facts instructions 34816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_35328 : Path.checkChunk context decode facts instructions 35328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_35840 : Path.checkChunk context decode facts instructions 35840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_36352 : Path.checkChunk context decode facts instructions 36352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_36864 : Path.checkChunk context decode facts instructions 36864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_37376 : Path.checkChunk context decode facts instructions 37376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_37888 : Path.checkChunk context decode facts instructions 37888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_38400 : Path.checkChunk context decode facts instructions 38400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_38912 : Path.checkChunk context decode facts instructions 38912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_39424 : Path.checkChunk context decode facts instructions 39424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_39936 : Path.checkChunk context decode facts instructions 39936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_40448 : Path.checkChunk context decode facts instructions 40448 512 = true := by
  decide +kernel

theorem sound_32768 (prior : ∀ n, n < 32768 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 40960 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h33280 := Path.chunk_sound context_valid decode facts instructions 32768 512
    prior checked_32768
  have h33792 := Path.chunk_sound context_valid decode facts instructions 33280 512
    h33280 checked_33280
  have h34304 := Path.chunk_sound context_valid decode facts instructions 33792 512
    h33792 checked_33792
  have h34816 := Path.chunk_sound context_valid decode facts instructions 34304 512
    h34304 checked_34304
  have h35328 := Path.chunk_sound context_valid decode facts instructions 34816 512
    h34816 checked_34816
  have h35840 := Path.chunk_sound context_valid decode facts instructions 35328 512
    h35328 checked_35328
  have h36352 := Path.chunk_sound context_valid decode facts instructions 35840 512
    h35840 checked_35840
  have h36864 := Path.chunk_sound context_valid decode facts instructions 36352 512
    h36352 checked_36352
  have h37376 := Path.chunk_sound context_valid decode facts instructions 36864 512
    h36864 checked_36864
  have h37888 := Path.chunk_sound context_valid decode facts instructions 37376 512
    h37376 checked_37376
  have h38400 := Path.chunk_sound context_valid decode facts instructions 37888 512
    h37888 checked_37888
  have h38912 := Path.chunk_sound context_valid decode facts instructions 38400 512
    h38400 checked_38400
  have h39424 := Path.chunk_sound context_valid decode facts instructions 38912 512
    h38912 checked_38912
  have h39936 := Path.chunk_sound context_valid decode facts instructions 39424 512
    h39424 checked_39424
  have h40448 := Path.chunk_sound context_valid decode facts instructions 39936 512
    h39936 checked_39936
  have h40960 := Path.chunk_sound context_valid decode facts instructions 40448 512
    h40448 checked_40448
  exact h40960

end Sporadic.Janko3.AmalgamPresentation.Cover
