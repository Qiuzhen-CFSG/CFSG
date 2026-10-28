module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1253376 : Path.checkChunk context decode facts instructions 1253376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1253888 : Path.checkChunk context decode facts instructions 1253888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1254400 : Path.checkChunk context decode facts instructions 1254400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1254912 : Path.checkChunk context decode facts instructions 1254912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1255424 : Path.checkChunk context decode facts instructions 1255424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1255936 : Path.checkChunk context decode facts instructions 1255936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1256448 : Path.checkChunk context decode facts instructions 1256448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1256960 : Path.checkChunk context decode facts instructions 1256960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1257472 : Path.checkChunk context decode facts instructions 1257472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1257984 : Path.checkChunk context decode facts instructions 1257984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1258496 : Path.checkChunk context decode facts instructions 1258496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1259008 : Path.checkChunk context decode facts instructions 1259008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1259520 : Path.checkChunk context decode facts instructions 1259520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1260032 : Path.checkChunk context decode facts instructions 1260032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1260544 : Path.checkChunk context decode facts instructions 1260544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1261056 : Path.checkChunk context decode facts instructions 1261056 512 = true := by
  decide +kernel

theorem sound_1253376 (prior : ∀ n, n < 1253376 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1261568 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1253888 := Path.chunk_sound context_valid decode facts instructions 1253376 512
    prior checked_1253376
  have h1254400 := Path.chunk_sound context_valid decode facts instructions 1253888 512
    h1253888 checked_1253888
  have h1254912 := Path.chunk_sound context_valid decode facts instructions 1254400 512
    h1254400 checked_1254400
  have h1255424 := Path.chunk_sound context_valid decode facts instructions 1254912 512
    h1254912 checked_1254912
  have h1255936 := Path.chunk_sound context_valid decode facts instructions 1255424 512
    h1255424 checked_1255424
  have h1256448 := Path.chunk_sound context_valid decode facts instructions 1255936 512
    h1255936 checked_1255936
  have h1256960 := Path.chunk_sound context_valid decode facts instructions 1256448 512
    h1256448 checked_1256448
  have h1257472 := Path.chunk_sound context_valid decode facts instructions 1256960 512
    h1256960 checked_1256960
  have h1257984 := Path.chunk_sound context_valid decode facts instructions 1257472 512
    h1257472 checked_1257472
  have h1258496 := Path.chunk_sound context_valid decode facts instructions 1257984 512
    h1257984 checked_1257984
  have h1259008 := Path.chunk_sound context_valid decode facts instructions 1258496 512
    h1258496 checked_1258496
  have h1259520 := Path.chunk_sound context_valid decode facts instructions 1259008 512
    h1259008 checked_1259008
  have h1260032 := Path.chunk_sound context_valid decode facts instructions 1259520 512
    h1259520 checked_1259520
  have h1260544 := Path.chunk_sound context_valid decode facts instructions 1260032 512
    h1260032 checked_1260032
  have h1261056 := Path.chunk_sound context_valid decode facts instructions 1260544 512
    h1260544 checked_1260544
  have h1261568 := Path.chunk_sound context_valid decode facts instructions 1261056 512
    h1261056 checked_1261056
  exact h1261568

end Sporadic.Janko3.AmalgamPresentation.Cover
