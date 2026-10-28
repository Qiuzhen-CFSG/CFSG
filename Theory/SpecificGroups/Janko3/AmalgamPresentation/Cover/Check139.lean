module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1138688 : Path.checkChunk context decode facts instructions 1138688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1139200 : Path.checkChunk context decode facts instructions 1139200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1139712 : Path.checkChunk context decode facts instructions 1139712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1140224 : Path.checkChunk context decode facts instructions 1140224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1140736 : Path.checkChunk context decode facts instructions 1140736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1141248 : Path.checkChunk context decode facts instructions 1141248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1141760 : Path.checkChunk context decode facts instructions 1141760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1142272 : Path.checkChunk context decode facts instructions 1142272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1142784 : Path.checkChunk context decode facts instructions 1142784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1143296 : Path.checkChunk context decode facts instructions 1143296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1143808 : Path.checkChunk context decode facts instructions 1143808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1144320 : Path.checkChunk context decode facts instructions 1144320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1144832 : Path.checkChunk context decode facts instructions 1144832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1145344 : Path.checkChunk context decode facts instructions 1145344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1145856 : Path.checkChunk context decode facts instructions 1145856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1146368 : Path.checkChunk context decode facts instructions 1146368 512 = true := by
  decide +kernel

theorem sound_1138688 (prior : ∀ n, n < 1138688 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1146880 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1139200 := Path.chunk_sound context_valid decode facts instructions 1138688 512
    prior checked_1138688
  have h1139712 := Path.chunk_sound context_valid decode facts instructions 1139200 512
    h1139200 checked_1139200
  have h1140224 := Path.chunk_sound context_valid decode facts instructions 1139712 512
    h1139712 checked_1139712
  have h1140736 := Path.chunk_sound context_valid decode facts instructions 1140224 512
    h1140224 checked_1140224
  have h1141248 := Path.chunk_sound context_valid decode facts instructions 1140736 512
    h1140736 checked_1140736
  have h1141760 := Path.chunk_sound context_valid decode facts instructions 1141248 512
    h1141248 checked_1141248
  have h1142272 := Path.chunk_sound context_valid decode facts instructions 1141760 512
    h1141760 checked_1141760
  have h1142784 := Path.chunk_sound context_valid decode facts instructions 1142272 512
    h1142272 checked_1142272
  have h1143296 := Path.chunk_sound context_valid decode facts instructions 1142784 512
    h1142784 checked_1142784
  have h1143808 := Path.chunk_sound context_valid decode facts instructions 1143296 512
    h1143296 checked_1143296
  have h1144320 := Path.chunk_sound context_valid decode facts instructions 1143808 512
    h1143808 checked_1143808
  have h1144832 := Path.chunk_sound context_valid decode facts instructions 1144320 512
    h1144320 checked_1144320
  have h1145344 := Path.chunk_sound context_valid decode facts instructions 1144832 512
    h1144832 checked_1144832
  have h1145856 := Path.chunk_sound context_valid decode facts instructions 1145344 512
    h1145344 checked_1145344
  have h1146368 := Path.chunk_sound context_valid decode facts instructions 1145856 512
    h1145856 checked_1145856
  have h1146880 := Path.chunk_sound context_valid decode facts instructions 1146368 512
    h1146368 checked_1146368
  exact h1146880

end Sporadic.Janko3.AmalgamPresentation.Cover
