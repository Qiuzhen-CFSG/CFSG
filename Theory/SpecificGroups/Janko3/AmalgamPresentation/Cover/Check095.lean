module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_778240 : Path.checkChunk context decode facts instructions 778240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_778752 : Path.checkChunk context decode facts instructions 778752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_779264 : Path.checkChunk context decode facts instructions 779264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_779776 : Path.checkChunk context decode facts instructions 779776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_780288 : Path.checkChunk context decode facts instructions 780288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_780800 : Path.checkChunk context decode facts instructions 780800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_781312 : Path.checkChunk context decode facts instructions 781312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_781824 : Path.checkChunk context decode facts instructions 781824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_782336 : Path.checkChunk context decode facts instructions 782336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_782848 : Path.checkChunk context decode facts instructions 782848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_783360 : Path.checkChunk context decode facts instructions 783360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_783872 : Path.checkChunk context decode facts instructions 783872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_784384 : Path.checkChunk context decode facts instructions 784384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_784896 : Path.checkChunk context decode facts instructions 784896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_785408 : Path.checkChunk context decode facts instructions 785408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_785920 : Path.checkChunk context decode facts instructions 785920 512 = true := by
  decide +kernel

theorem sound_778240 (prior : ∀ n, n < 778240 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 786432 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h778752 := Path.chunk_sound context_valid decode facts instructions 778240 512
    prior checked_778240
  have h779264 := Path.chunk_sound context_valid decode facts instructions 778752 512
    h778752 checked_778752
  have h779776 := Path.chunk_sound context_valid decode facts instructions 779264 512
    h779264 checked_779264
  have h780288 := Path.chunk_sound context_valid decode facts instructions 779776 512
    h779776 checked_779776
  have h780800 := Path.chunk_sound context_valid decode facts instructions 780288 512
    h780288 checked_780288
  have h781312 := Path.chunk_sound context_valid decode facts instructions 780800 512
    h780800 checked_780800
  have h781824 := Path.chunk_sound context_valid decode facts instructions 781312 512
    h781312 checked_781312
  have h782336 := Path.chunk_sound context_valid decode facts instructions 781824 512
    h781824 checked_781824
  have h782848 := Path.chunk_sound context_valid decode facts instructions 782336 512
    h782336 checked_782336
  have h783360 := Path.chunk_sound context_valid decode facts instructions 782848 512
    h782848 checked_782848
  have h783872 := Path.chunk_sound context_valid decode facts instructions 783360 512
    h783360 checked_783360
  have h784384 := Path.chunk_sound context_valid decode facts instructions 783872 512
    h783872 checked_783872
  have h784896 := Path.chunk_sound context_valid decode facts instructions 784384 512
    h784384 checked_784384
  have h785408 := Path.chunk_sound context_valid decode facts instructions 784896 512
    h784896 checked_784896
  have h785920 := Path.chunk_sound context_valid decode facts instructions 785408 512
    h785408 checked_785408
  have h786432 := Path.chunk_sound context_valid decode facts instructions 785920 512
    h785920 checked_785920
  exact h786432

end Sporadic.Janko3.AmalgamPresentation.Cover
