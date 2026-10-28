module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1392640 : Path.checkChunk context decode facts instructions 1392640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1393152 : Path.checkChunk context decode facts instructions 1393152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1393664 : Path.checkChunk context decode facts instructions 1393664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1394176 : Path.checkChunk context decode facts instructions 1394176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1394688 : Path.checkChunk context decode facts instructions 1394688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1395200 : Path.checkChunk context decode facts instructions 1395200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1395712 : Path.checkChunk context decode facts instructions 1395712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1396224 : Path.checkChunk context decode facts instructions 1396224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1396736 : Path.checkChunk context decode facts instructions 1396736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1397248 : Path.checkChunk context decode facts instructions 1397248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1397760 : Path.checkChunk context decode facts instructions 1397760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1398272 : Path.checkChunk context decode facts instructions 1398272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1398784 : Path.checkChunk context decode facts instructions 1398784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1399296 : Path.checkChunk context decode facts instructions 1399296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1399808 : Path.checkChunk context decode facts instructions 1399808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1400320 : Path.checkChunk context decode facts instructions 1400320 512 = true := by
  decide +kernel

theorem sound_1392640 (prior : ∀ n, n < 1392640 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1400832 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1393152 := Path.chunk_sound context_valid decode facts instructions 1392640 512
    prior checked_1392640
  have h1393664 := Path.chunk_sound context_valid decode facts instructions 1393152 512
    h1393152 checked_1393152
  have h1394176 := Path.chunk_sound context_valid decode facts instructions 1393664 512
    h1393664 checked_1393664
  have h1394688 := Path.chunk_sound context_valid decode facts instructions 1394176 512
    h1394176 checked_1394176
  have h1395200 := Path.chunk_sound context_valid decode facts instructions 1394688 512
    h1394688 checked_1394688
  have h1395712 := Path.chunk_sound context_valid decode facts instructions 1395200 512
    h1395200 checked_1395200
  have h1396224 := Path.chunk_sound context_valid decode facts instructions 1395712 512
    h1395712 checked_1395712
  have h1396736 := Path.chunk_sound context_valid decode facts instructions 1396224 512
    h1396224 checked_1396224
  have h1397248 := Path.chunk_sound context_valid decode facts instructions 1396736 512
    h1396736 checked_1396736
  have h1397760 := Path.chunk_sound context_valid decode facts instructions 1397248 512
    h1397248 checked_1397248
  have h1398272 := Path.chunk_sound context_valid decode facts instructions 1397760 512
    h1397760 checked_1397760
  have h1398784 := Path.chunk_sound context_valid decode facts instructions 1398272 512
    h1398272 checked_1398272
  have h1399296 := Path.chunk_sound context_valid decode facts instructions 1398784 512
    h1398784 checked_1398784
  have h1399808 := Path.chunk_sound context_valid decode facts instructions 1399296 512
    h1399296 checked_1399296
  have h1400320 := Path.chunk_sound context_valid decode facts instructions 1399808 512
    h1399808 checked_1399808
  have h1400832 := Path.chunk_sound context_valid decode facts instructions 1400320 512
    h1400320 checked_1400320
  exact h1400832

end Sporadic.Janko3.AmalgamPresentation.Cover
