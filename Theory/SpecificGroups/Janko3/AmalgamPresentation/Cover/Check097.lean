module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_794624 : Path.checkChunk context decode facts instructions 794624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_795136 : Path.checkChunk context decode facts instructions 795136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_795648 : Path.checkChunk context decode facts instructions 795648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_796160 : Path.checkChunk context decode facts instructions 796160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_796672 : Path.checkChunk context decode facts instructions 796672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_797184 : Path.checkChunk context decode facts instructions 797184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_797696 : Path.checkChunk context decode facts instructions 797696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_798208 : Path.checkChunk context decode facts instructions 798208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_798720 : Path.checkChunk context decode facts instructions 798720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_799232 : Path.checkChunk context decode facts instructions 799232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_799744 : Path.checkChunk context decode facts instructions 799744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_800256 : Path.checkChunk context decode facts instructions 800256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_800768 : Path.checkChunk context decode facts instructions 800768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_801280 : Path.checkChunk context decode facts instructions 801280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_801792 : Path.checkChunk context decode facts instructions 801792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_802304 : Path.checkChunk context decode facts instructions 802304 512 = true := by
  decide +kernel

theorem sound_794624 (prior : ∀ n, n < 794624 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 802816 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h795136 := Path.chunk_sound context_valid decode facts instructions 794624 512
    prior checked_794624
  have h795648 := Path.chunk_sound context_valid decode facts instructions 795136 512
    h795136 checked_795136
  have h796160 := Path.chunk_sound context_valid decode facts instructions 795648 512
    h795648 checked_795648
  have h796672 := Path.chunk_sound context_valid decode facts instructions 796160 512
    h796160 checked_796160
  have h797184 := Path.chunk_sound context_valid decode facts instructions 796672 512
    h796672 checked_796672
  have h797696 := Path.chunk_sound context_valid decode facts instructions 797184 512
    h797184 checked_797184
  have h798208 := Path.chunk_sound context_valid decode facts instructions 797696 512
    h797696 checked_797696
  have h798720 := Path.chunk_sound context_valid decode facts instructions 798208 512
    h798208 checked_798208
  have h799232 := Path.chunk_sound context_valid decode facts instructions 798720 512
    h798720 checked_798720
  have h799744 := Path.chunk_sound context_valid decode facts instructions 799232 512
    h799232 checked_799232
  have h800256 := Path.chunk_sound context_valid decode facts instructions 799744 512
    h799744 checked_799744
  have h800768 := Path.chunk_sound context_valid decode facts instructions 800256 512
    h800256 checked_800256
  have h801280 := Path.chunk_sound context_valid decode facts instructions 800768 512
    h800768 checked_800768
  have h801792 := Path.chunk_sound context_valid decode facts instructions 801280 512
    h801280 checked_801280
  have h802304 := Path.chunk_sound context_valid decode facts instructions 801792 512
    h801792 checked_801792
  have h802816 := Path.chunk_sound context_valid decode facts instructions 802304 512
    h802304 checked_802304
  exact h802816

end Sporadic.Janko3.AmalgamPresentation.Cover
