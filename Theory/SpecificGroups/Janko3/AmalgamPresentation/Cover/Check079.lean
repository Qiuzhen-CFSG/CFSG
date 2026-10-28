module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_647168 : Path.checkChunk context decode facts instructions 647168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_647680 : Path.checkChunk context decode facts instructions 647680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_648192 : Path.checkChunk context decode facts instructions 648192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_648704 : Path.checkChunk context decode facts instructions 648704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_649216 : Path.checkChunk context decode facts instructions 649216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_649728 : Path.checkChunk context decode facts instructions 649728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_650240 : Path.checkChunk context decode facts instructions 650240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_650752 : Path.checkChunk context decode facts instructions 650752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_651264 : Path.checkChunk context decode facts instructions 651264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_651776 : Path.checkChunk context decode facts instructions 651776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_652288 : Path.checkChunk context decode facts instructions 652288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_652800 : Path.checkChunk context decode facts instructions 652800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_653312 : Path.checkChunk context decode facts instructions 653312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_653824 : Path.checkChunk context decode facts instructions 653824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_654336 : Path.checkChunk context decode facts instructions 654336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_654848 : Path.checkChunk context decode facts instructions 654848 512 = true := by
  decide +kernel

theorem sound_647168 (prior : ∀ n, n < 647168 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 655360 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h647680 := Path.chunk_sound context_valid decode facts instructions 647168 512
    prior checked_647168
  have h648192 := Path.chunk_sound context_valid decode facts instructions 647680 512
    h647680 checked_647680
  have h648704 := Path.chunk_sound context_valid decode facts instructions 648192 512
    h648192 checked_648192
  have h649216 := Path.chunk_sound context_valid decode facts instructions 648704 512
    h648704 checked_648704
  have h649728 := Path.chunk_sound context_valid decode facts instructions 649216 512
    h649216 checked_649216
  have h650240 := Path.chunk_sound context_valid decode facts instructions 649728 512
    h649728 checked_649728
  have h650752 := Path.chunk_sound context_valid decode facts instructions 650240 512
    h650240 checked_650240
  have h651264 := Path.chunk_sound context_valid decode facts instructions 650752 512
    h650752 checked_650752
  have h651776 := Path.chunk_sound context_valid decode facts instructions 651264 512
    h651264 checked_651264
  have h652288 := Path.chunk_sound context_valid decode facts instructions 651776 512
    h651776 checked_651776
  have h652800 := Path.chunk_sound context_valid decode facts instructions 652288 512
    h652288 checked_652288
  have h653312 := Path.chunk_sound context_valid decode facts instructions 652800 512
    h652800 checked_652800
  have h653824 := Path.chunk_sound context_valid decode facts instructions 653312 512
    h653312 checked_653312
  have h654336 := Path.chunk_sound context_valid decode facts instructions 653824 512
    h653824 checked_653824
  have h654848 := Path.chunk_sound context_valid decode facts instructions 654336 512
    h654336 checked_654336
  have h655360 := Path.chunk_sound context_valid decode facts instructions 654848 512
    h654848 checked_654848
  exact h655360

end Sporadic.Janko3.AmalgamPresentation.Cover
