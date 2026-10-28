module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1196032 : Path.checkChunk context decode facts instructions 1196032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1196544 : Path.checkChunk context decode facts instructions 1196544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1197056 : Path.checkChunk context decode facts instructions 1197056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1197568 : Path.checkChunk context decode facts instructions 1197568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1198080 : Path.checkChunk context decode facts instructions 1198080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1198592 : Path.checkChunk context decode facts instructions 1198592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1199104 : Path.checkChunk context decode facts instructions 1199104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1199616 : Path.checkChunk context decode facts instructions 1199616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1200128 : Path.checkChunk context decode facts instructions 1200128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1200640 : Path.checkChunk context decode facts instructions 1200640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1201152 : Path.checkChunk context decode facts instructions 1201152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1201664 : Path.checkChunk context decode facts instructions 1201664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1202176 : Path.checkChunk context decode facts instructions 1202176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1202688 : Path.checkChunk context decode facts instructions 1202688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1203200 : Path.checkChunk context decode facts instructions 1203200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1203712 : Path.checkChunk context decode facts instructions 1203712 512 = true := by
  decide +kernel

theorem sound_1196032 (prior : ∀ n, n < 1196032 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1204224 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1196544 := Path.chunk_sound context_valid decode facts instructions 1196032 512
    prior checked_1196032
  have h1197056 := Path.chunk_sound context_valid decode facts instructions 1196544 512
    h1196544 checked_1196544
  have h1197568 := Path.chunk_sound context_valid decode facts instructions 1197056 512
    h1197056 checked_1197056
  have h1198080 := Path.chunk_sound context_valid decode facts instructions 1197568 512
    h1197568 checked_1197568
  have h1198592 := Path.chunk_sound context_valid decode facts instructions 1198080 512
    h1198080 checked_1198080
  have h1199104 := Path.chunk_sound context_valid decode facts instructions 1198592 512
    h1198592 checked_1198592
  have h1199616 := Path.chunk_sound context_valid decode facts instructions 1199104 512
    h1199104 checked_1199104
  have h1200128 := Path.chunk_sound context_valid decode facts instructions 1199616 512
    h1199616 checked_1199616
  have h1200640 := Path.chunk_sound context_valid decode facts instructions 1200128 512
    h1200128 checked_1200128
  have h1201152 := Path.chunk_sound context_valid decode facts instructions 1200640 512
    h1200640 checked_1200640
  have h1201664 := Path.chunk_sound context_valid decode facts instructions 1201152 512
    h1201152 checked_1201152
  have h1202176 := Path.chunk_sound context_valid decode facts instructions 1201664 512
    h1201664 checked_1201664
  have h1202688 := Path.chunk_sound context_valid decode facts instructions 1202176 512
    h1202176 checked_1202176
  have h1203200 := Path.chunk_sound context_valid decode facts instructions 1202688 512
    h1202688 checked_1202688
  have h1203712 := Path.chunk_sound context_valid decode facts instructions 1203200 512
    h1203200 checked_1203200
  have h1204224 := Path.chunk_sound context_valid decode facts instructions 1203712 512
    h1203712 checked_1203712
  exact h1204224

end Sporadic.Janko3.AmalgamPresentation.Cover
