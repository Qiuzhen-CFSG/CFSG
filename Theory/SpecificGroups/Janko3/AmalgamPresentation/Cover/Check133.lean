module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1089536 : Path.checkChunk context decode facts instructions 1089536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1090048 : Path.checkChunk context decode facts instructions 1090048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1090560 : Path.checkChunk context decode facts instructions 1090560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1091072 : Path.checkChunk context decode facts instructions 1091072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1091584 : Path.checkChunk context decode facts instructions 1091584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1092096 : Path.checkChunk context decode facts instructions 1092096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1092608 : Path.checkChunk context decode facts instructions 1092608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1093120 : Path.checkChunk context decode facts instructions 1093120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1093632 : Path.checkChunk context decode facts instructions 1093632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1094144 : Path.checkChunk context decode facts instructions 1094144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1094656 : Path.checkChunk context decode facts instructions 1094656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1095168 : Path.checkChunk context decode facts instructions 1095168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1095680 : Path.checkChunk context decode facts instructions 1095680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1096192 : Path.checkChunk context decode facts instructions 1096192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1096704 : Path.checkChunk context decode facts instructions 1096704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1097216 : Path.checkChunk context decode facts instructions 1097216 512 = true := by
  decide +kernel

theorem sound_1089536 (prior : ∀ n, n < 1089536 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1097728 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1090048 := Path.chunk_sound context_valid decode facts instructions 1089536 512
    prior checked_1089536
  have h1090560 := Path.chunk_sound context_valid decode facts instructions 1090048 512
    h1090048 checked_1090048
  have h1091072 := Path.chunk_sound context_valid decode facts instructions 1090560 512
    h1090560 checked_1090560
  have h1091584 := Path.chunk_sound context_valid decode facts instructions 1091072 512
    h1091072 checked_1091072
  have h1092096 := Path.chunk_sound context_valid decode facts instructions 1091584 512
    h1091584 checked_1091584
  have h1092608 := Path.chunk_sound context_valid decode facts instructions 1092096 512
    h1092096 checked_1092096
  have h1093120 := Path.chunk_sound context_valid decode facts instructions 1092608 512
    h1092608 checked_1092608
  have h1093632 := Path.chunk_sound context_valid decode facts instructions 1093120 512
    h1093120 checked_1093120
  have h1094144 := Path.chunk_sound context_valid decode facts instructions 1093632 512
    h1093632 checked_1093632
  have h1094656 := Path.chunk_sound context_valid decode facts instructions 1094144 512
    h1094144 checked_1094144
  have h1095168 := Path.chunk_sound context_valid decode facts instructions 1094656 512
    h1094656 checked_1094656
  have h1095680 := Path.chunk_sound context_valid decode facts instructions 1095168 512
    h1095168 checked_1095168
  have h1096192 := Path.chunk_sound context_valid decode facts instructions 1095680 512
    h1095680 checked_1095680
  have h1096704 := Path.chunk_sound context_valid decode facts instructions 1096192 512
    h1096192 checked_1096192
  have h1097216 := Path.chunk_sound context_valid decode facts instructions 1096704 512
    h1096704 checked_1096704
  have h1097728 := Path.chunk_sound context_valid decode facts instructions 1097216 512
    h1097216 checked_1097216
  exact h1097728

end Sporadic.Janko3.AmalgamPresentation.Cover
