module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_917504 : Path.checkChunk context decode facts instructions 917504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_918016 : Path.checkChunk context decode facts instructions 918016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_918528 : Path.checkChunk context decode facts instructions 918528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_919040 : Path.checkChunk context decode facts instructions 919040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_919552 : Path.checkChunk context decode facts instructions 919552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_920064 : Path.checkChunk context decode facts instructions 920064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_920576 : Path.checkChunk context decode facts instructions 920576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_921088 : Path.checkChunk context decode facts instructions 921088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_921600 : Path.checkChunk context decode facts instructions 921600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_922112 : Path.checkChunk context decode facts instructions 922112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_922624 : Path.checkChunk context decode facts instructions 922624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_923136 : Path.checkChunk context decode facts instructions 923136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_923648 : Path.checkChunk context decode facts instructions 923648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_924160 : Path.checkChunk context decode facts instructions 924160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_924672 : Path.checkChunk context decode facts instructions 924672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_925184 : Path.checkChunk context decode facts instructions 925184 512 = true := by
  decide +kernel

theorem sound_917504 (prior : ∀ n, n < 917504 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 925696 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h918016 := Path.chunk_sound context_valid decode facts instructions 917504 512
    prior checked_917504
  have h918528 := Path.chunk_sound context_valid decode facts instructions 918016 512
    h918016 checked_918016
  have h919040 := Path.chunk_sound context_valid decode facts instructions 918528 512
    h918528 checked_918528
  have h919552 := Path.chunk_sound context_valid decode facts instructions 919040 512
    h919040 checked_919040
  have h920064 := Path.chunk_sound context_valid decode facts instructions 919552 512
    h919552 checked_919552
  have h920576 := Path.chunk_sound context_valid decode facts instructions 920064 512
    h920064 checked_920064
  have h921088 := Path.chunk_sound context_valid decode facts instructions 920576 512
    h920576 checked_920576
  have h921600 := Path.chunk_sound context_valid decode facts instructions 921088 512
    h921088 checked_921088
  have h922112 := Path.chunk_sound context_valid decode facts instructions 921600 512
    h921600 checked_921600
  have h922624 := Path.chunk_sound context_valid decode facts instructions 922112 512
    h922112 checked_922112
  have h923136 := Path.chunk_sound context_valid decode facts instructions 922624 512
    h922624 checked_922624
  have h923648 := Path.chunk_sound context_valid decode facts instructions 923136 512
    h923136 checked_923136
  have h924160 := Path.chunk_sound context_valid decode facts instructions 923648 512
    h923648 checked_923648
  have h924672 := Path.chunk_sound context_valid decode facts instructions 924160 512
    h924160 checked_924160
  have h925184 := Path.chunk_sound context_valid decode facts instructions 924672 512
    h924672 checked_924672
  have h925696 := Path.chunk_sound context_valid decode facts instructions 925184 512
    h925184 checked_925184
  exact h925696

end Sporadic.Janko3.AmalgamPresentation.Cover
