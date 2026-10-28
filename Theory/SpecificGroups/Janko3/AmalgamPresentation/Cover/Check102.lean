module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_835584 : Path.checkChunk context decode facts instructions 835584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_836096 : Path.checkChunk context decode facts instructions 836096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_836608 : Path.checkChunk context decode facts instructions 836608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_837120 : Path.checkChunk context decode facts instructions 837120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_837632 : Path.checkChunk context decode facts instructions 837632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_838144 : Path.checkChunk context decode facts instructions 838144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_838656 : Path.checkChunk context decode facts instructions 838656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_839168 : Path.checkChunk context decode facts instructions 839168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_839680 : Path.checkChunk context decode facts instructions 839680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_840192 : Path.checkChunk context decode facts instructions 840192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_840704 : Path.checkChunk context decode facts instructions 840704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_841216 : Path.checkChunk context decode facts instructions 841216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_841728 : Path.checkChunk context decode facts instructions 841728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_842240 : Path.checkChunk context decode facts instructions 842240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_842752 : Path.checkChunk context decode facts instructions 842752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_843264 : Path.checkChunk context decode facts instructions 843264 512 = true := by
  decide +kernel

theorem sound_835584 (prior : ∀ n, n < 835584 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 843776 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h836096 := Path.chunk_sound context_valid decode facts instructions 835584 512
    prior checked_835584
  have h836608 := Path.chunk_sound context_valid decode facts instructions 836096 512
    h836096 checked_836096
  have h837120 := Path.chunk_sound context_valid decode facts instructions 836608 512
    h836608 checked_836608
  have h837632 := Path.chunk_sound context_valid decode facts instructions 837120 512
    h837120 checked_837120
  have h838144 := Path.chunk_sound context_valid decode facts instructions 837632 512
    h837632 checked_837632
  have h838656 := Path.chunk_sound context_valid decode facts instructions 838144 512
    h838144 checked_838144
  have h839168 := Path.chunk_sound context_valid decode facts instructions 838656 512
    h838656 checked_838656
  have h839680 := Path.chunk_sound context_valid decode facts instructions 839168 512
    h839168 checked_839168
  have h840192 := Path.chunk_sound context_valid decode facts instructions 839680 512
    h839680 checked_839680
  have h840704 := Path.chunk_sound context_valid decode facts instructions 840192 512
    h840192 checked_840192
  have h841216 := Path.chunk_sound context_valid decode facts instructions 840704 512
    h840704 checked_840704
  have h841728 := Path.chunk_sound context_valid decode facts instructions 841216 512
    h841216 checked_841216
  have h842240 := Path.chunk_sound context_valid decode facts instructions 841728 512
    h841728 checked_841728
  have h842752 := Path.chunk_sound context_valid decode facts instructions 842240 512
    h842240 checked_842240
  have h843264 := Path.chunk_sound context_valid decode facts instructions 842752 512
    h842752 checked_842752
  have h843776 := Path.chunk_sound context_valid decode facts instructions 843264 512
    h843264 checked_843264
  exact h843776

end Sporadic.Janko3.AmalgamPresentation.Cover
