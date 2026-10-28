module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_131072 : Path.checkChunk context decode facts instructions 131072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_131584 : Path.checkChunk context decode facts instructions 131584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_132096 : Path.checkChunk context decode facts instructions 132096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_132608 : Path.checkChunk context decode facts instructions 132608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_133120 : Path.checkChunk context decode facts instructions 133120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_133632 : Path.checkChunk context decode facts instructions 133632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_134144 : Path.checkChunk context decode facts instructions 134144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_134656 : Path.checkChunk context decode facts instructions 134656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_135168 : Path.checkChunk context decode facts instructions 135168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_135680 : Path.checkChunk context decode facts instructions 135680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_136192 : Path.checkChunk context decode facts instructions 136192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_136704 : Path.checkChunk context decode facts instructions 136704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_137216 : Path.checkChunk context decode facts instructions 137216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_137728 : Path.checkChunk context decode facts instructions 137728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_138240 : Path.checkChunk context decode facts instructions 138240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_138752 : Path.checkChunk context decode facts instructions 138752 512 = true := by
  decide +kernel

theorem sound_131072 (prior : ∀ n, n < 131072 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 139264 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h131584 := Path.chunk_sound context_valid decode facts instructions 131072 512
    prior checked_131072
  have h132096 := Path.chunk_sound context_valid decode facts instructions 131584 512
    h131584 checked_131584
  have h132608 := Path.chunk_sound context_valid decode facts instructions 132096 512
    h132096 checked_132096
  have h133120 := Path.chunk_sound context_valid decode facts instructions 132608 512
    h132608 checked_132608
  have h133632 := Path.chunk_sound context_valid decode facts instructions 133120 512
    h133120 checked_133120
  have h134144 := Path.chunk_sound context_valid decode facts instructions 133632 512
    h133632 checked_133632
  have h134656 := Path.chunk_sound context_valid decode facts instructions 134144 512
    h134144 checked_134144
  have h135168 := Path.chunk_sound context_valid decode facts instructions 134656 512
    h134656 checked_134656
  have h135680 := Path.chunk_sound context_valid decode facts instructions 135168 512
    h135168 checked_135168
  have h136192 := Path.chunk_sound context_valid decode facts instructions 135680 512
    h135680 checked_135680
  have h136704 := Path.chunk_sound context_valid decode facts instructions 136192 512
    h136192 checked_136192
  have h137216 := Path.chunk_sound context_valid decode facts instructions 136704 512
    h136704 checked_136704
  have h137728 := Path.chunk_sound context_valid decode facts instructions 137216 512
    h137216 checked_137216
  have h138240 := Path.chunk_sound context_valid decode facts instructions 137728 512
    h137728 checked_137728
  have h138752 := Path.chunk_sound context_valid decode facts instructions 138240 512
    h138240 checked_138240
  have h139264 := Path.chunk_sound context_valid decode facts instructions 138752 512
    h138752 checked_138752
  exact h139264

end Sporadic.Janko3.AmalgamPresentation.Cover
