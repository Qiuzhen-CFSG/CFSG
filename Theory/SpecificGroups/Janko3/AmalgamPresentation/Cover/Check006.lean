module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_49152 : Path.checkChunk context decode facts instructions 49152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_49664 : Path.checkChunk context decode facts instructions 49664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_50176 : Path.checkChunk context decode facts instructions 50176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_50688 : Path.checkChunk context decode facts instructions 50688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_51200 : Path.checkChunk context decode facts instructions 51200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_51712 : Path.checkChunk context decode facts instructions 51712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_52224 : Path.checkChunk context decode facts instructions 52224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_52736 : Path.checkChunk context decode facts instructions 52736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_53248 : Path.checkChunk context decode facts instructions 53248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_53760 : Path.checkChunk context decode facts instructions 53760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_54272 : Path.checkChunk context decode facts instructions 54272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_54784 : Path.checkChunk context decode facts instructions 54784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_55296 : Path.checkChunk context decode facts instructions 55296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_55808 : Path.checkChunk context decode facts instructions 55808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_56320 : Path.checkChunk context decode facts instructions 56320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_56832 : Path.checkChunk context decode facts instructions 56832 512 = true := by
  decide +kernel

theorem sound_49152 (prior : ∀ n, n < 49152 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 57344 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h49664 := Path.chunk_sound context_valid decode facts instructions 49152 512
    prior checked_49152
  have h50176 := Path.chunk_sound context_valid decode facts instructions 49664 512
    h49664 checked_49664
  have h50688 := Path.chunk_sound context_valid decode facts instructions 50176 512
    h50176 checked_50176
  have h51200 := Path.chunk_sound context_valid decode facts instructions 50688 512
    h50688 checked_50688
  have h51712 := Path.chunk_sound context_valid decode facts instructions 51200 512
    h51200 checked_51200
  have h52224 := Path.chunk_sound context_valid decode facts instructions 51712 512
    h51712 checked_51712
  have h52736 := Path.chunk_sound context_valid decode facts instructions 52224 512
    h52224 checked_52224
  have h53248 := Path.chunk_sound context_valid decode facts instructions 52736 512
    h52736 checked_52736
  have h53760 := Path.chunk_sound context_valid decode facts instructions 53248 512
    h53248 checked_53248
  have h54272 := Path.chunk_sound context_valid decode facts instructions 53760 512
    h53760 checked_53760
  have h54784 := Path.chunk_sound context_valid decode facts instructions 54272 512
    h54272 checked_54272
  have h55296 := Path.chunk_sound context_valid decode facts instructions 54784 512
    h54784 checked_54784
  have h55808 := Path.chunk_sound context_valid decode facts instructions 55296 512
    h55296 checked_55296
  have h56320 := Path.chunk_sound context_valid decode facts instructions 55808 512
    h55808 checked_55808
  have h56832 := Path.chunk_sound context_valid decode facts instructions 56320 512
    h56320 checked_56320
  have h57344 := Path.chunk_sound context_valid decode facts instructions 56832 512
    h56832 checked_56832
  exact h57344

end Sporadic.Janko3.AmalgamPresentation.Cover
