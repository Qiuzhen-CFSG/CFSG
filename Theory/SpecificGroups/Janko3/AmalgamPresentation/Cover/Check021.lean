module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_172032 : Path.checkChunk context decode facts instructions 172032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_172544 : Path.checkChunk context decode facts instructions 172544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_173056 : Path.checkChunk context decode facts instructions 173056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_173568 : Path.checkChunk context decode facts instructions 173568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_174080 : Path.checkChunk context decode facts instructions 174080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_174592 : Path.checkChunk context decode facts instructions 174592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_175104 : Path.checkChunk context decode facts instructions 175104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_175616 : Path.checkChunk context decode facts instructions 175616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_176128 : Path.checkChunk context decode facts instructions 176128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_176640 : Path.checkChunk context decode facts instructions 176640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_177152 : Path.checkChunk context decode facts instructions 177152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_177664 : Path.checkChunk context decode facts instructions 177664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_178176 : Path.checkChunk context decode facts instructions 178176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_178688 : Path.checkChunk context decode facts instructions 178688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_179200 : Path.checkChunk context decode facts instructions 179200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_179712 : Path.checkChunk context decode facts instructions 179712 512 = true := by
  decide +kernel

theorem sound_172032 (prior : ∀ n, n < 172032 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 180224 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h172544 := Path.chunk_sound context_valid decode facts instructions 172032 512
    prior checked_172032
  have h173056 := Path.chunk_sound context_valid decode facts instructions 172544 512
    h172544 checked_172544
  have h173568 := Path.chunk_sound context_valid decode facts instructions 173056 512
    h173056 checked_173056
  have h174080 := Path.chunk_sound context_valid decode facts instructions 173568 512
    h173568 checked_173568
  have h174592 := Path.chunk_sound context_valid decode facts instructions 174080 512
    h174080 checked_174080
  have h175104 := Path.chunk_sound context_valid decode facts instructions 174592 512
    h174592 checked_174592
  have h175616 := Path.chunk_sound context_valid decode facts instructions 175104 512
    h175104 checked_175104
  have h176128 := Path.chunk_sound context_valid decode facts instructions 175616 512
    h175616 checked_175616
  have h176640 := Path.chunk_sound context_valid decode facts instructions 176128 512
    h176128 checked_176128
  have h177152 := Path.chunk_sound context_valid decode facts instructions 176640 512
    h176640 checked_176640
  have h177664 := Path.chunk_sound context_valid decode facts instructions 177152 512
    h177152 checked_177152
  have h178176 := Path.chunk_sound context_valid decode facts instructions 177664 512
    h177664 checked_177664
  have h178688 := Path.chunk_sound context_valid decode facts instructions 178176 512
    h178176 checked_178176
  have h179200 := Path.chunk_sound context_valid decode facts instructions 178688 512
    h178688 checked_178688
  have h179712 := Path.chunk_sound context_valid decode facts instructions 179200 512
    h179200 checked_179200
  have h180224 := Path.chunk_sound context_valid decode facts instructions 179712 512
    h179712 checked_179712
  exact h180224

end Sporadic.Janko3.AmalgamPresentation.Cover
