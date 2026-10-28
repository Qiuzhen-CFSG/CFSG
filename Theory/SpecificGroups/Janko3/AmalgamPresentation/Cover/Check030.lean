module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_245760 : Path.checkChunk context decode facts instructions 245760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_246272 : Path.checkChunk context decode facts instructions 246272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_246784 : Path.checkChunk context decode facts instructions 246784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_247296 : Path.checkChunk context decode facts instructions 247296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_247808 : Path.checkChunk context decode facts instructions 247808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_248320 : Path.checkChunk context decode facts instructions 248320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_248832 : Path.checkChunk context decode facts instructions 248832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_249344 : Path.checkChunk context decode facts instructions 249344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_249856 : Path.checkChunk context decode facts instructions 249856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_250368 : Path.checkChunk context decode facts instructions 250368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_250880 : Path.checkChunk context decode facts instructions 250880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_251392 : Path.checkChunk context decode facts instructions 251392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_251904 : Path.checkChunk context decode facts instructions 251904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_252416 : Path.checkChunk context decode facts instructions 252416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_252928 : Path.checkChunk context decode facts instructions 252928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_253440 : Path.checkChunk context decode facts instructions 253440 512 = true := by
  decide +kernel

theorem sound_245760 (prior : ∀ n, n < 245760 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 253952 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h246272 := Path.chunk_sound context_valid decode facts instructions 245760 512
    prior checked_245760
  have h246784 := Path.chunk_sound context_valid decode facts instructions 246272 512
    h246272 checked_246272
  have h247296 := Path.chunk_sound context_valid decode facts instructions 246784 512
    h246784 checked_246784
  have h247808 := Path.chunk_sound context_valid decode facts instructions 247296 512
    h247296 checked_247296
  have h248320 := Path.chunk_sound context_valid decode facts instructions 247808 512
    h247808 checked_247808
  have h248832 := Path.chunk_sound context_valid decode facts instructions 248320 512
    h248320 checked_248320
  have h249344 := Path.chunk_sound context_valid decode facts instructions 248832 512
    h248832 checked_248832
  have h249856 := Path.chunk_sound context_valid decode facts instructions 249344 512
    h249344 checked_249344
  have h250368 := Path.chunk_sound context_valid decode facts instructions 249856 512
    h249856 checked_249856
  have h250880 := Path.chunk_sound context_valid decode facts instructions 250368 512
    h250368 checked_250368
  have h251392 := Path.chunk_sound context_valid decode facts instructions 250880 512
    h250880 checked_250880
  have h251904 := Path.chunk_sound context_valid decode facts instructions 251392 512
    h251392 checked_251392
  have h252416 := Path.chunk_sound context_valid decode facts instructions 251904 512
    h251904 checked_251904
  have h252928 := Path.chunk_sound context_valid decode facts instructions 252416 512
    h252416 checked_252416
  have h253440 := Path.chunk_sound context_valid decode facts instructions 252928 512
    h252928 checked_252928
  have h253952 := Path.chunk_sound context_valid decode facts instructions 253440 512
    h253440 checked_253440
  exact h253952

end Sporadic.Janko3.AmalgamPresentation.Cover
