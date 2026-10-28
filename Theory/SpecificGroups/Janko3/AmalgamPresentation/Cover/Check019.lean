module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_155648 : Path.checkChunk context decode facts instructions 155648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_156160 : Path.checkChunk context decode facts instructions 156160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_156672 : Path.checkChunk context decode facts instructions 156672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_157184 : Path.checkChunk context decode facts instructions 157184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_157696 : Path.checkChunk context decode facts instructions 157696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_158208 : Path.checkChunk context decode facts instructions 158208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_158720 : Path.checkChunk context decode facts instructions 158720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_159232 : Path.checkChunk context decode facts instructions 159232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_159744 : Path.checkChunk context decode facts instructions 159744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_160256 : Path.checkChunk context decode facts instructions 160256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_160768 : Path.checkChunk context decode facts instructions 160768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_161280 : Path.checkChunk context decode facts instructions 161280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_161792 : Path.checkChunk context decode facts instructions 161792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_162304 : Path.checkChunk context decode facts instructions 162304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_162816 : Path.checkChunk context decode facts instructions 162816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_163328 : Path.checkChunk context decode facts instructions 163328 512 = true := by
  decide +kernel

theorem sound_155648 (prior : ∀ n, n < 155648 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 163840 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h156160 := Path.chunk_sound context_valid decode facts instructions 155648 512
    prior checked_155648
  have h156672 := Path.chunk_sound context_valid decode facts instructions 156160 512
    h156160 checked_156160
  have h157184 := Path.chunk_sound context_valid decode facts instructions 156672 512
    h156672 checked_156672
  have h157696 := Path.chunk_sound context_valid decode facts instructions 157184 512
    h157184 checked_157184
  have h158208 := Path.chunk_sound context_valid decode facts instructions 157696 512
    h157696 checked_157696
  have h158720 := Path.chunk_sound context_valid decode facts instructions 158208 512
    h158208 checked_158208
  have h159232 := Path.chunk_sound context_valid decode facts instructions 158720 512
    h158720 checked_158720
  have h159744 := Path.chunk_sound context_valid decode facts instructions 159232 512
    h159232 checked_159232
  have h160256 := Path.chunk_sound context_valid decode facts instructions 159744 512
    h159744 checked_159744
  have h160768 := Path.chunk_sound context_valid decode facts instructions 160256 512
    h160256 checked_160256
  have h161280 := Path.chunk_sound context_valid decode facts instructions 160768 512
    h160768 checked_160768
  have h161792 := Path.chunk_sound context_valid decode facts instructions 161280 512
    h161280 checked_161280
  have h162304 := Path.chunk_sound context_valid decode facts instructions 161792 512
    h161792 checked_161792
  have h162816 := Path.chunk_sound context_valid decode facts instructions 162304 512
    h162304 checked_162304
  have h163328 := Path.chunk_sound context_valid decode facts instructions 162816 512
    h162816 checked_162816
  have h163840 := Path.chunk_sound context_valid decode facts instructions 163328 512
    h163328 checked_163328
  exact h163840

end Sporadic.Janko3.AmalgamPresentation.Cover
