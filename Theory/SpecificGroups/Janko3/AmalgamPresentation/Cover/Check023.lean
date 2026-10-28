module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_188416 : Path.checkChunk context decode facts instructions 188416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_188928 : Path.checkChunk context decode facts instructions 188928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_189440 : Path.checkChunk context decode facts instructions 189440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_189952 : Path.checkChunk context decode facts instructions 189952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_190464 : Path.checkChunk context decode facts instructions 190464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_190976 : Path.checkChunk context decode facts instructions 190976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_191488 : Path.checkChunk context decode facts instructions 191488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_192000 : Path.checkChunk context decode facts instructions 192000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_192512 : Path.checkChunk context decode facts instructions 192512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_193024 : Path.checkChunk context decode facts instructions 193024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_193536 : Path.checkChunk context decode facts instructions 193536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_194048 : Path.checkChunk context decode facts instructions 194048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_194560 : Path.checkChunk context decode facts instructions 194560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_195072 : Path.checkChunk context decode facts instructions 195072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_195584 : Path.checkChunk context decode facts instructions 195584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_196096 : Path.checkChunk context decode facts instructions 196096 512 = true := by
  decide +kernel

theorem sound_188416 (prior : ∀ n, n < 188416 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 196608 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h188928 := Path.chunk_sound context_valid decode facts instructions 188416 512
    prior checked_188416
  have h189440 := Path.chunk_sound context_valid decode facts instructions 188928 512
    h188928 checked_188928
  have h189952 := Path.chunk_sound context_valid decode facts instructions 189440 512
    h189440 checked_189440
  have h190464 := Path.chunk_sound context_valid decode facts instructions 189952 512
    h189952 checked_189952
  have h190976 := Path.chunk_sound context_valid decode facts instructions 190464 512
    h190464 checked_190464
  have h191488 := Path.chunk_sound context_valid decode facts instructions 190976 512
    h190976 checked_190976
  have h192000 := Path.chunk_sound context_valid decode facts instructions 191488 512
    h191488 checked_191488
  have h192512 := Path.chunk_sound context_valid decode facts instructions 192000 512
    h192000 checked_192000
  have h193024 := Path.chunk_sound context_valid decode facts instructions 192512 512
    h192512 checked_192512
  have h193536 := Path.chunk_sound context_valid decode facts instructions 193024 512
    h193024 checked_193024
  have h194048 := Path.chunk_sound context_valid decode facts instructions 193536 512
    h193536 checked_193536
  have h194560 := Path.chunk_sound context_valid decode facts instructions 194048 512
    h194048 checked_194048
  have h195072 := Path.chunk_sound context_valid decode facts instructions 194560 512
    h194560 checked_194560
  have h195584 := Path.chunk_sound context_valid decode facts instructions 195072 512
    h195072 checked_195072
  have h196096 := Path.chunk_sound context_valid decode facts instructions 195584 512
    h195584 checked_195584
  have h196608 := Path.chunk_sound context_valid decode facts instructions 196096 512
    h196096 checked_196096
  exact h196608

end Sporadic.Janko3.AmalgamPresentation.Cover
