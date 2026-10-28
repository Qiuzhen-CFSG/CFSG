module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_884736 : Path.checkChunk context decode facts instructions 884736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_885248 : Path.checkChunk context decode facts instructions 885248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_885760 : Path.checkChunk context decode facts instructions 885760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_886272 : Path.checkChunk context decode facts instructions 886272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_886784 : Path.checkChunk context decode facts instructions 886784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_887296 : Path.checkChunk context decode facts instructions 887296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_887808 : Path.checkChunk context decode facts instructions 887808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_888320 : Path.checkChunk context decode facts instructions 888320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_888832 : Path.checkChunk context decode facts instructions 888832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_889344 : Path.checkChunk context decode facts instructions 889344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_889856 : Path.checkChunk context decode facts instructions 889856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_890368 : Path.checkChunk context decode facts instructions 890368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_890880 : Path.checkChunk context decode facts instructions 890880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_891392 : Path.checkChunk context decode facts instructions 891392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_891904 : Path.checkChunk context decode facts instructions 891904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_892416 : Path.checkChunk context decode facts instructions 892416 512 = true := by
  decide +kernel

theorem sound_884736 (prior : ∀ n, n < 884736 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 892928 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h885248 := Path.chunk_sound context_valid decode facts instructions 884736 512
    prior checked_884736
  have h885760 := Path.chunk_sound context_valid decode facts instructions 885248 512
    h885248 checked_885248
  have h886272 := Path.chunk_sound context_valid decode facts instructions 885760 512
    h885760 checked_885760
  have h886784 := Path.chunk_sound context_valid decode facts instructions 886272 512
    h886272 checked_886272
  have h887296 := Path.chunk_sound context_valid decode facts instructions 886784 512
    h886784 checked_886784
  have h887808 := Path.chunk_sound context_valid decode facts instructions 887296 512
    h887296 checked_887296
  have h888320 := Path.chunk_sound context_valid decode facts instructions 887808 512
    h887808 checked_887808
  have h888832 := Path.chunk_sound context_valid decode facts instructions 888320 512
    h888320 checked_888320
  have h889344 := Path.chunk_sound context_valid decode facts instructions 888832 512
    h888832 checked_888832
  have h889856 := Path.chunk_sound context_valid decode facts instructions 889344 512
    h889344 checked_889344
  have h890368 := Path.chunk_sound context_valid decode facts instructions 889856 512
    h889856 checked_889856
  have h890880 := Path.chunk_sound context_valid decode facts instructions 890368 512
    h890368 checked_890368
  have h891392 := Path.chunk_sound context_valid decode facts instructions 890880 512
    h890880 checked_890880
  have h891904 := Path.chunk_sound context_valid decode facts instructions 891392 512
    h891392 checked_891392
  have h892416 := Path.chunk_sound context_valid decode facts instructions 891904 512
    h891904 checked_891904
  have h892928 := Path.chunk_sound context_valid decode facts instructions 892416 512
    h892416 checked_892416
  exact h892928

end Sporadic.Janko3.AmalgamPresentation.Cover
