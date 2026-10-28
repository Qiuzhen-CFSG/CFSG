module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_81920 : Path.checkChunk context decode facts instructions 81920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_82432 : Path.checkChunk context decode facts instructions 82432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_82944 : Path.checkChunk context decode facts instructions 82944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_83456 : Path.checkChunk context decode facts instructions 83456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_83968 : Path.checkChunk context decode facts instructions 83968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_84480 : Path.checkChunk context decode facts instructions 84480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_84992 : Path.checkChunk context decode facts instructions 84992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_85504 : Path.checkChunk context decode facts instructions 85504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_86016 : Path.checkChunk context decode facts instructions 86016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_86528 : Path.checkChunk context decode facts instructions 86528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_87040 : Path.checkChunk context decode facts instructions 87040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_87552 : Path.checkChunk context decode facts instructions 87552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_88064 : Path.checkChunk context decode facts instructions 88064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_88576 : Path.checkChunk context decode facts instructions 88576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_89088 : Path.checkChunk context decode facts instructions 89088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_89600 : Path.checkChunk context decode facts instructions 89600 512 = true := by
  decide +kernel

theorem sound_81920 (prior : ∀ n, n < 81920 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 90112 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h82432 := Path.chunk_sound context_valid decode facts instructions 81920 512
    prior checked_81920
  have h82944 := Path.chunk_sound context_valid decode facts instructions 82432 512
    h82432 checked_82432
  have h83456 := Path.chunk_sound context_valid decode facts instructions 82944 512
    h82944 checked_82944
  have h83968 := Path.chunk_sound context_valid decode facts instructions 83456 512
    h83456 checked_83456
  have h84480 := Path.chunk_sound context_valid decode facts instructions 83968 512
    h83968 checked_83968
  have h84992 := Path.chunk_sound context_valid decode facts instructions 84480 512
    h84480 checked_84480
  have h85504 := Path.chunk_sound context_valid decode facts instructions 84992 512
    h84992 checked_84992
  have h86016 := Path.chunk_sound context_valid decode facts instructions 85504 512
    h85504 checked_85504
  have h86528 := Path.chunk_sound context_valid decode facts instructions 86016 512
    h86016 checked_86016
  have h87040 := Path.chunk_sound context_valid decode facts instructions 86528 512
    h86528 checked_86528
  have h87552 := Path.chunk_sound context_valid decode facts instructions 87040 512
    h87040 checked_87040
  have h88064 := Path.chunk_sound context_valid decode facts instructions 87552 512
    h87552 checked_87552
  have h88576 := Path.chunk_sound context_valid decode facts instructions 88064 512
    h88064 checked_88064
  have h89088 := Path.chunk_sound context_valid decode facts instructions 88576 512
    h88576 checked_88576
  have h89600 := Path.chunk_sound context_valid decode facts instructions 89088 512
    h89088 checked_89088
  have h90112 := Path.chunk_sound context_valid decode facts instructions 89600 512
    h89600 checked_89600
  exact h90112

end Sporadic.Janko3.AmalgamPresentation.Cover
