module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_73728 : Path.checkChunk context decode facts instructions 73728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_74240 : Path.checkChunk context decode facts instructions 74240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_74752 : Path.checkChunk context decode facts instructions 74752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_75264 : Path.checkChunk context decode facts instructions 75264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_75776 : Path.checkChunk context decode facts instructions 75776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_76288 : Path.checkChunk context decode facts instructions 76288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_76800 : Path.checkChunk context decode facts instructions 76800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_77312 : Path.checkChunk context decode facts instructions 77312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_77824 : Path.checkChunk context decode facts instructions 77824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_78336 : Path.checkChunk context decode facts instructions 78336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_78848 : Path.checkChunk context decode facts instructions 78848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_79360 : Path.checkChunk context decode facts instructions 79360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_79872 : Path.checkChunk context decode facts instructions 79872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_80384 : Path.checkChunk context decode facts instructions 80384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_80896 : Path.checkChunk context decode facts instructions 80896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_81408 : Path.checkChunk context decode facts instructions 81408 512 = true := by
  decide +kernel

theorem sound_73728 (prior : ∀ n, n < 73728 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 81920 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h74240 := Path.chunk_sound context_valid decode facts instructions 73728 512
    prior checked_73728
  have h74752 := Path.chunk_sound context_valid decode facts instructions 74240 512
    h74240 checked_74240
  have h75264 := Path.chunk_sound context_valid decode facts instructions 74752 512
    h74752 checked_74752
  have h75776 := Path.chunk_sound context_valid decode facts instructions 75264 512
    h75264 checked_75264
  have h76288 := Path.chunk_sound context_valid decode facts instructions 75776 512
    h75776 checked_75776
  have h76800 := Path.chunk_sound context_valid decode facts instructions 76288 512
    h76288 checked_76288
  have h77312 := Path.chunk_sound context_valid decode facts instructions 76800 512
    h76800 checked_76800
  have h77824 := Path.chunk_sound context_valid decode facts instructions 77312 512
    h77312 checked_77312
  have h78336 := Path.chunk_sound context_valid decode facts instructions 77824 512
    h77824 checked_77824
  have h78848 := Path.chunk_sound context_valid decode facts instructions 78336 512
    h78336 checked_78336
  have h79360 := Path.chunk_sound context_valid decode facts instructions 78848 512
    h78848 checked_78848
  have h79872 := Path.chunk_sound context_valid decode facts instructions 79360 512
    h79360 checked_79360
  have h80384 := Path.chunk_sound context_valid decode facts instructions 79872 512
    h79872 checked_79872
  have h80896 := Path.chunk_sound context_valid decode facts instructions 80384 512
    h80384 checked_80384
  have h81408 := Path.chunk_sound context_valid decode facts instructions 80896 512
    h80896 checked_80896
  have h81920 := Path.chunk_sound context_valid decode facts instructions 81408 512
    h81408 checked_81408
  exact h81920

end Sporadic.Janko3.AmalgamPresentation.Cover
