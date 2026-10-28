module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_286720 : Path.checkChunk context decode facts instructions 286720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_287232 : Path.checkChunk context decode facts instructions 287232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_287744 : Path.checkChunk context decode facts instructions 287744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_288256 : Path.checkChunk context decode facts instructions 288256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_288768 : Path.checkChunk context decode facts instructions 288768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_289280 : Path.checkChunk context decode facts instructions 289280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_289792 : Path.checkChunk context decode facts instructions 289792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_290304 : Path.checkChunk context decode facts instructions 290304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_290816 : Path.checkChunk context decode facts instructions 290816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_291328 : Path.checkChunk context decode facts instructions 291328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_291840 : Path.checkChunk context decode facts instructions 291840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_292352 : Path.checkChunk context decode facts instructions 292352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_292864 : Path.checkChunk context decode facts instructions 292864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_293376 : Path.checkChunk context decode facts instructions 293376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_293888 : Path.checkChunk context decode facts instructions 293888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_294400 : Path.checkChunk context decode facts instructions 294400 512 = true := by
  decide +kernel

theorem sound_286720 (prior : ∀ n, n < 286720 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 294912 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h287232 := Path.chunk_sound context_valid decode facts instructions 286720 512
    prior checked_286720
  have h287744 := Path.chunk_sound context_valid decode facts instructions 287232 512
    h287232 checked_287232
  have h288256 := Path.chunk_sound context_valid decode facts instructions 287744 512
    h287744 checked_287744
  have h288768 := Path.chunk_sound context_valid decode facts instructions 288256 512
    h288256 checked_288256
  have h289280 := Path.chunk_sound context_valid decode facts instructions 288768 512
    h288768 checked_288768
  have h289792 := Path.chunk_sound context_valid decode facts instructions 289280 512
    h289280 checked_289280
  have h290304 := Path.chunk_sound context_valid decode facts instructions 289792 512
    h289792 checked_289792
  have h290816 := Path.chunk_sound context_valid decode facts instructions 290304 512
    h290304 checked_290304
  have h291328 := Path.chunk_sound context_valid decode facts instructions 290816 512
    h290816 checked_290816
  have h291840 := Path.chunk_sound context_valid decode facts instructions 291328 512
    h291328 checked_291328
  have h292352 := Path.chunk_sound context_valid decode facts instructions 291840 512
    h291840 checked_291840
  have h292864 := Path.chunk_sound context_valid decode facts instructions 292352 512
    h292352 checked_292352
  have h293376 := Path.chunk_sound context_valid decode facts instructions 292864 512
    h292864 checked_292864
  have h293888 := Path.chunk_sound context_valid decode facts instructions 293376 512
    h293376 checked_293376
  have h294400 := Path.chunk_sound context_valid decode facts instructions 293888 512
    h293888 checked_293888
  have h294912 := Path.chunk_sound context_valid decode facts instructions 294400 512
    h294400 checked_294400
  exact h294912

end Sporadic.Janko3.AmalgamPresentation.Cover
