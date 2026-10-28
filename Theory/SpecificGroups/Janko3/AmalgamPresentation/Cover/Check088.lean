module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_720896 : Path.checkChunk context decode facts instructions 720896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_721408 : Path.checkChunk context decode facts instructions 721408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_721920 : Path.checkChunk context decode facts instructions 721920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_722432 : Path.checkChunk context decode facts instructions 722432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_722944 : Path.checkChunk context decode facts instructions 722944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_723456 : Path.checkChunk context decode facts instructions 723456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_723968 : Path.checkChunk context decode facts instructions 723968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_724480 : Path.checkChunk context decode facts instructions 724480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_724992 : Path.checkChunk context decode facts instructions 724992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_725504 : Path.checkChunk context decode facts instructions 725504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_726016 : Path.checkChunk context decode facts instructions 726016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_726528 : Path.checkChunk context decode facts instructions 726528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_727040 : Path.checkChunk context decode facts instructions 727040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_727552 : Path.checkChunk context decode facts instructions 727552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_728064 : Path.checkChunk context decode facts instructions 728064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_728576 : Path.checkChunk context decode facts instructions 728576 512 = true := by
  decide +kernel

theorem sound_720896 (prior : ∀ n, n < 720896 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 729088 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h721408 := Path.chunk_sound context_valid decode facts instructions 720896 512
    prior checked_720896
  have h721920 := Path.chunk_sound context_valid decode facts instructions 721408 512
    h721408 checked_721408
  have h722432 := Path.chunk_sound context_valid decode facts instructions 721920 512
    h721920 checked_721920
  have h722944 := Path.chunk_sound context_valid decode facts instructions 722432 512
    h722432 checked_722432
  have h723456 := Path.chunk_sound context_valid decode facts instructions 722944 512
    h722944 checked_722944
  have h723968 := Path.chunk_sound context_valid decode facts instructions 723456 512
    h723456 checked_723456
  have h724480 := Path.chunk_sound context_valid decode facts instructions 723968 512
    h723968 checked_723968
  have h724992 := Path.chunk_sound context_valid decode facts instructions 724480 512
    h724480 checked_724480
  have h725504 := Path.chunk_sound context_valid decode facts instructions 724992 512
    h724992 checked_724992
  have h726016 := Path.chunk_sound context_valid decode facts instructions 725504 512
    h725504 checked_725504
  have h726528 := Path.chunk_sound context_valid decode facts instructions 726016 512
    h726016 checked_726016
  have h727040 := Path.chunk_sound context_valid decode facts instructions 726528 512
    h726528 checked_726528
  have h727552 := Path.chunk_sound context_valid decode facts instructions 727040 512
    h727040 checked_727040
  have h728064 := Path.chunk_sound context_valid decode facts instructions 727552 512
    h727552 checked_727552
  have h728576 := Path.chunk_sound context_valid decode facts instructions 728064 512
    h728064 checked_728064
  have h729088 := Path.chunk_sound context_valid decode facts instructions 728576 512
    h728576 checked_728576
  exact h729088

end Sporadic.Janko3.AmalgamPresentation.Cover
