module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_303104 : Path.checkChunk context decode facts instructions 303104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_303616 : Path.checkChunk context decode facts instructions 303616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_304128 : Path.checkChunk context decode facts instructions 304128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_304640 : Path.checkChunk context decode facts instructions 304640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_305152 : Path.checkChunk context decode facts instructions 305152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_305664 : Path.checkChunk context decode facts instructions 305664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_306176 : Path.checkChunk context decode facts instructions 306176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_306688 : Path.checkChunk context decode facts instructions 306688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_307200 : Path.checkChunk context decode facts instructions 307200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_307712 : Path.checkChunk context decode facts instructions 307712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_308224 : Path.checkChunk context decode facts instructions 308224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_308736 : Path.checkChunk context decode facts instructions 308736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_309248 : Path.checkChunk context decode facts instructions 309248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_309760 : Path.checkChunk context decode facts instructions 309760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_310272 : Path.checkChunk context decode facts instructions 310272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_310784 : Path.checkChunk context decode facts instructions 310784 512 = true := by
  decide +kernel

theorem sound_303104 (prior : ∀ n, n < 303104 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 311296 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h303616 := Path.chunk_sound context_valid decode facts instructions 303104 512
    prior checked_303104
  have h304128 := Path.chunk_sound context_valid decode facts instructions 303616 512
    h303616 checked_303616
  have h304640 := Path.chunk_sound context_valid decode facts instructions 304128 512
    h304128 checked_304128
  have h305152 := Path.chunk_sound context_valid decode facts instructions 304640 512
    h304640 checked_304640
  have h305664 := Path.chunk_sound context_valid decode facts instructions 305152 512
    h305152 checked_305152
  have h306176 := Path.chunk_sound context_valid decode facts instructions 305664 512
    h305664 checked_305664
  have h306688 := Path.chunk_sound context_valid decode facts instructions 306176 512
    h306176 checked_306176
  have h307200 := Path.chunk_sound context_valid decode facts instructions 306688 512
    h306688 checked_306688
  have h307712 := Path.chunk_sound context_valid decode facts instructions 307200 512
    h307200 checked_307200
  have h308224 := Path.chunk_sound context_valid decode facts instructions 307712 512
    h307712 checked_307712
  have h308736 := Path.chunk_sound context_valid decode facts instructions 308224 512
    h308224 checked_308224
  have h309248 := Path.chunk_sound context_valid decode facts instructions 308736 512
    h308736 checked_308736
  have h309760 := Path.chunk_sound context_valid decode facts instructions 309248 512
    h309248 checked_309248
  have h310272 := Path.chunk_sound context_valid decode facts instructions 309760 512
    h309760 checked_309760
  have h310784 := Path.chunk_sound context_valid decode facts instructions 310272 512
    h310272 checked_310272
  have h311296 := Path.chunk_sound context_valid decode facts instructions 310784 512
    h310784 checked_310784
  exact h311296

end Sporadic.Janko3.AmalgamPresentation.Cover
