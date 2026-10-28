module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1024000 : Path.checkChunk context decode facts instructions 1024000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1024512 : Path.checkChunk context decode facts instructions 1024512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1025024 : Path.checkChunk context decode facts instructions 1025024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1025536 : Path.checkChunk context decode facts instructions 1025536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1026048 : Path.checkChunk context decode facts instructions 1026048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1026560 : Path.checkChunk context decode facts instructions 1026560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1027072 : Path.checkChunk context decode facts instructions 1027072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1027584 : Path.checkChunk context decode facts instructions 1027584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1028096 : Path.checkChunk context decode facts instructions 1028096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1028608 : Path.checkChunk context decode facts instructions 1028608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1029120 : Path.checkChunk context decode facts instructions 1029120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1029632 : Path.checkChunk context decode facts instructions 1029632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1030144 : Path.checkChunk context decode facts instructions 1030144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1030656 : Path.checkChunk context decode facts instructions 1030656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1031168 : Path.checkChunk context decode facts instructions 1031168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1031680 : Path.checkChunk context decode facts instructions 1031680 512 = true := by
  decide +kernel

theorem sound_1024000 (prior : ∀ n, n < 1024000 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1032192 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1024512 := Path.chunk_sound context_valid decode facts instructions 1024000 512
    prior checked_1024000
  have h1025024 := Path.chunk_sound context_valid decode facts instructions 1024512 512
    h1024512 checked_1024512
  have h1025536 := Path.chunk_sound context_valid decode facts instructions 1025024 512
    h1025024 checked_1025024
  have h1026048 := Path.chunk_sound context_valid decode facts instructions 1025536 512
    h1025536 checked_1025536
  have h1026560 := Path.chunk_sound context_valid decode facts instructions 1026048 512
    h1026048 checked_1026048
  have h1027072 := Path.chunk_sound context_valid decode facts instructions 1026560 512
    h1026560 checked_1026560
  have h1027584 := Path.chunk_sound context_valid decode facts instructions 1027072 512
    h1027072 checked_1027072
  have h1028096 := Path.chunk_sound context_valid decode facts instructions 1027584 512
    h1027584 checked_1027584
  have h1028608 := Path.chunk_sound context_valid decode facts instructions 1028096 512
    h1028096 checked_1028096
  have h1029120 := Path.chunk_sound context_valid decode facts instructions 1028608 512
    h1028608 checked_1028608
  have h1029632 := Path.chunk_sound context_valid decode facts instructions 1029120 512
    h1029120 checked_1029120
  have h1030144 := Path.chunk_sound context_valid decode facts instructions 1029632 512
    h1029632 checked_1029632
  have h1030656 := Path.chunk_sound context_valid decode facts instructions 1030144 512
    h1030144 checked_1030144
  have h1031168 := Path.chunk_sound context_valid decode facts instructions 1030656 512
    h1030656 checked_1030656
  have h1031680 := Path.chunk_sound context_valid decode facts instructions 1031168 512
    h1031168 checked_1031168
  have h1032192 := Path.chunk_sound context_valid decode facts instructions 1031680 512
    h1031680 checked_1031680
  exact h1032192

end Sporadic.Janko3.AmalgamPresentation.Cover
