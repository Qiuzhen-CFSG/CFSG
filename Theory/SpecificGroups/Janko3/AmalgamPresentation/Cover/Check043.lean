module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_352256 : Path.checkChunk context decode facts instructions 352256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_352768 : Path.checkChunk context decode facts instructions 352768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_353280 : Path.checkChunk context decode facts instructions 353280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_353792 : Path.checkChunk context decode facts instructions 353792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_354304 : Path.checkChunk context decode facts instructions 354304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_354816 : Path.checkChunk context decode facts instructions 354816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_355328 : Path.checkChunk context decode facts instructions 355328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_355840 : Path.checkChunk context decode facts instructions 355840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_356352 : Path.checkChunk context decode facts instructions 356352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_356864 : Path.checkChunk context decode facts instructions 356864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_357376 : Path.checkChunk context decode facts instructions 357376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_357888 : Path.checkChunk context decode facts instructions 357888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_358400 : Path.checkChunk context decode facts instructions 358400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_358912 : Path.checkChunk context decode facts instructions 358912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_359424 : Path.checkChunk context decode facts instructions 359424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_359936 : Path.checkChunk context decode facts instructions 359936 512 = true := by
  decide +kernel

theorem sound_352256 (prior : ∀ n, n < 352256 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 360448 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h352768 := Path.chunk_sound context_valid decode facts instructions 352256 512
    prior checked_352256
  have h353280 := Path.chunk_sound context_valid decode facts instructions 352768 512
    h352768 checked_352768
  have h353792 := Path.chunk_sound context_valid decode facts instructions 353280 512
    h353280 checked_353280
  have h354304 := Path.chunk_sound context_valid decode facts instructions 353792 512
    h353792 checked_353792
  have h354816 := Path.chunk_sound context_valid decode facts instructions 354304 512
    h354304 checked_354304
  have h355328 := Path.chunk_sound context_valid decode facts instructions 354816 512
    h354816 checked_354816
  have h355840 := Path.chunk_sound context_valid decode facts instructions 355328 512
    h355328 checked_355328
  have h356352 := Path.chunk_sound context_valid decode facts instructions 355840 512
    h355840 checked_355840
  have h356864 := Path.chunk_sound context_valid decode facts instructions 356352 512
    h356352 checked_356352
  have h357376 := Path.chunk_sound context_valid decode facts instructions 356864 512
    h356864 checked_356864
  have h357888 := Path.chunk_sound context_valid decode facts instructions 357376 512
    h357376 checked_357376
  have h358400 := Path.chunk_sound context_valid decode facts instructions 357888 512
    h357888 checked_357888
  have h358912 := Path.chunk_sound context_valid decode facts instructions 358400 512
    h358400 checked_358400
  have h359424 := Path.chunk_sound context_valid decode facts instructions 358912 512
    h358912 checked_358912
  have h359936 := Path.chunk_sound context_valid decode facts instructions 359424 512
    h359424 checked_359424
  have h360448 := Path.chunk_sound context_valid decode facts instructions 359936 512
    h359936 checked_359936
  exact h360448

end Sporadic.Janko3.AmalgamPresentation.Cover
