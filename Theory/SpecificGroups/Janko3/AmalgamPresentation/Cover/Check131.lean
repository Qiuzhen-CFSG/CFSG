module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1073152 : Path.checkChunk context decode facts instructions 1073152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1073664 : Path.checkChunk context decode facts instructions 1073664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1074176 : Path.checkChunk context decode facts instructions 1074176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1074688 : Path.checkChunk context decode facts instructions 1074688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1075200 : Path.checkChunk context decode facts instructions 1075200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1075712 : Path.checkChunk context decode facts instructions 1075712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1076224 : Path.checkChunk context decode facts instructions 1076224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1076736 : Path.checkChunk context decode facts instructions 1076736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1077248 : Path.checkChunk context decode facts instructions 1077248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1077760 : Path.checkChunk context decode facts instructions 1077760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1078272 : Path.checkChunk context decode facts instructions 1078272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1078784 : Path.checkChunk context decode facts instructions 1078784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1079296 : Path.checkChunk context decode facts instructions 1079296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1079808 : Path.checkChunk context decode facts instructions 1079808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1080320 : Path.checkChunk context decode facts instructions 1080320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1080832 : Path.checkChunk context decode facts instructions 1080832 512 = true := by
  decide +kernel

theorem sound_1073152 (prior : ∀ n, n < 1073152 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1081344 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1073664 := Path.chunk_sound context_valid decode facts instructions 1073152 512
    prior checked_1073152
  have h1074176 := Path.chunk_sound context_valid decode facts instructions 1073664 512
    h1073664 checked_1073664
  have h1074688 := Path.chunk_sound context_valid decode facts instructions 1074176 512
    h1074176 checked_1074176
  have h1075200 := Path.chunk_sound context_valid decode facts instructions 1074688 512
    h1074688 checked_1074688
  have h1075712 := Path.chunk_sound context_valid decode facts instructions 1075200 512
    h1075200 checked_1075200
  have h1076224 := Path.chunk_sound context_valid decode facts instructions 1075712 512
    h1075712 checked_1075712
  have h1076736 := Path.chunk_sound context_valid decode facts instructions 1076224 512
    h1076224 checked_1076224
  have h1077248 := Path.chunk_sound context_valid decode facts instructions 1076736 512
    h1076736 checked_1076736
  have h1077760 := Path.chunk_sound context_valid decode facts instructions 1077248 512
    h1077248 checked_1077248
  have h1078272 := Path.chunk_sound context_valid decode facts instructions 1077760 512
    h1077760 checked_1077760
  have h1078784 := Path.chunk_sound context_valid decode facts instructions 1078272 512
    h1078272 checked_1078272
  have h1079296 := Path.chunk_sound context_valid decode facts instructions 1078784 512
    h1078784 checked_1078784
  have h1079808 := Path.chunk_sound context_valid decode facts instructions 1079296 512
    h1079296 checked_1079296
  have h1080320 := Path.chunk_sound context_valid decode facts instructions 1079808 512
    h1079808 checked_1079808
  have h1080832 := Path.chunk_sound context_valid decode facts instructions 1080320 512
    h1080320 checked_1080320
  have h1081344 := Path.chunk_sound context_valid decode facts instructions 1080832 512
    h1080832 checked_1080832
  exact h1081344

end Sporadic.Janko3.AmalgamPresentation.Cover
