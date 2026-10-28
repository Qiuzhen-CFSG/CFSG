module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_565248 : Path.checkChunk context decode facts instructions 565248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_565760 : Path.checkChunk context decode facts instructions 565760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_566272 : Path.checkChunk context decode facts instructions 566272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_566784 : Path.checkChunk context decode facts instructions 566784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_567296 : Path.checkChunk context decode facts instructions 567296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_567808 : Path.checkChunk context decode facts instructions 567808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_568320 : Path.checkChunk context decode facts instructions 568320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_568832 : Path.checkChunk context decode facts instructions 568832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_569344 : Path.checkChunk context decode facts instructions 569344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_569856 : Path.checkChunk context decode facts instructions 569856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_570368 : Path.checkChunk context decode facts instructions 570368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_570880 : Path.checkChunk context decode facts instructions 570880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_571392 : Path.checkChunk context decode facts instructions 571392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_571904 : Path.checkChunk context decode facts instructions 571904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_572416 : Path.checkChunk context decode facts instructions 572416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_572928 : Path.checkChunk context decode facts instructions 572928 512 = true := by
  decide +kernel

theorem sound_565248 (prior : ∀ n, n < 565248 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 573440 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h565760 := Path.chunk_sound context_valid decode facts instructions 565248 512
    prior checked_565248
  have h566272 := Path.chunk_sound context_valid decode facts instructions 565760 512
    h565760 checked_565760
  have h566784 := Path.chunk_sound context_valid decode facts instructions 566272 512
    h566272 checked_566272
  have h567296 := Path.chunk_sound context_valid decode facts instructions 566784 512
    h566784 checked_566784
  have h567808 := Path.chunk_sound context_valid decode facts instructions 567296 512
    h567296 checked_567296
  have h568320 := Path.chunk_sound context_valid decode facts instructions 567808 512
    h567808 checked_567808
  have h568832 := Path.chunk_sound context_valid decode facts instructions 568320 512
    h568320 checked_568320
  have h569344 := Path.chunk_sound context_valid decode facts instructions 568832 512
    h568832 checked_568832
  have h569856 := Path.chunk_sound context_valid decode facts instructions 569344 512
    h569344 checked_569344
  have h570368 := Path.chunk_sound context_valid decode facts instructions 569856 512
    h569856 checked_569856
  have h570880 := Path.chunk_sound context_valid decode facts instructions 570368 512
    h570368 checked_570368
  have h571392 := Path.chunk_sound context_valid decode facts instructions 570880 512
    h570880 checked_570880
  have h571904 := Path.chunk_sound context_valid decode facts instructions 571392 512
    h571392 checked_571392
  have h572416 := Path.chunk_sound context_valid decode facts instructions 571904 512
    h571904 checked_571904
  have h572928 := Path.chunk_sound context_valid decode facts instructions 572416 512
    h572416 checked_572416
  have h573440 := Path.chunk_sound context_valid decode facts instructions 572928 512
    h572928 checked_572928
  exact h573440

end Sporadic.Janko3.AmalgamPresentation.Cover
