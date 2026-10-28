module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1081344 : Path.checkChunk context decode facts instructions 1081344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1081856 : Path.checkChunk context decode facts instructions 1081856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1082368 : Path.checkChunk context decode facts instructions 1082368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1082880 : Path.checkChunk context decode facts instructions 1082880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1083392 : Path.checkChunk context decode facts instructions 1083392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1083904 : Path.checkChunk context decode facts instructions 1083904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1084416 : Path.checkChunk context decode facts instructions 1084416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1084928 : Path.checkChunk context decode facts instructions 1084928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1085440 : Path.checkChunk context decode facts instructions 1085440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1085952 : Path.checkChunk context decode facts instructions 1085952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1086464 : Path.checkChunk context decode facts instructions 1086464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1086976 : Path.checkChunk context decode facts instructions 1086976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1087488 : Path.checkChunk context decode facts instructions 1087488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1088000 : Path.checkChunk context decode facts instructions 1088000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1088512 : Path.checkChunk context decode facts instructions 1088512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1089024 : Path.checkChunk context decode facts instructions 1089024 512 = true := by
  decide +kernel

theorem sound_1081344 (prior : ∀ n, n < 1081344 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1089536 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1081856 := Path.chunk_sound context_valid decode facts instructions 1081344 512
    prior checked_1081344
  have h1082368 := Path.chunk_sound context_valid decode facts instructions 1081856 512
    h1081856 checked_1081856
  have h1082880 := Path.chunk_sound context_valid decode facts instructions 1082368 512
    h1082368 checked_1082368
  have h1083392 := Path.chunk_sound context_valid decode facts instructions 1082880 512
    h1082880 checked_1082880
  have h1083904 := Path.chunk_sound context_valid decode facts instructions 1083392 512
    h1083392 checked_1083392
  have h1084416 := Path.chunk_sound context_valid decode facts instructions 1083904 512
    h1083904 checked_1083904
  have h1084928 := Path.chunk_sound context_valid decode facts instructions 1084416 512
    h1084416 checked_1084416
  have h1085440 := Path.chunk_sound context_valid decode facts instructions 1084928 512
    h1084928 checked_1084928
  have h1085952 := Path.chunk_sound context_valid decode facts instructions 1085440 512
    h1085440 checked_1085440
  have h1086464 := Path.chunk_sound context_valid decode facts instructions 1085952 512
    h1085952 checked_1085952
  have h1086976 := Path.chunk_sound context_valid decode facts instructions 1086464 512
    h1086464 checked_1086464
  have h1087488 := Path.chunk_sound context_valid decode facts instructions 1086976 512
    h1086976 checked_1086976
  have h1088000 := Path.chunk_sound context_valid decode facts instructions 1087488 512
    h1087488 checked_1087488
  have h1088512 := Path.chunk_sound context_valid decode facts instructions 1088000 512
    h1088000 checked_1088000
  have h1089024 := Path.chunk_sound context_valid decode facts instructions 1088512 512
    h1088512 checked_1088512
  have h1089536 := Path.chunk_sound context_valid decode facts instructions 1089024 512
    h1089024 checked_1089024
  exact h1089536

end Sporadic.Janko3.AmalgamPresentation.Cover
