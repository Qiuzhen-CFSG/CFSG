module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_622592 : Path.checkChunk context decode facts instructions 622592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_623104 : Path.checkChunk context decode facts instructions 623104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_623616 : Path.checkChunk context decode facts instructions 623616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_624128 : Path.checkChunk context decode facts instructions 624128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_624640 : Path.checkChunk context decode facts instructions 624640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_625152 : Path.checkChunk context decode facts instructions 625152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_625664 : Path.checkChunk context decode facts instructions 625664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_626176 : Path.checkChunk context decode facts instructions 626176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_626688 : Path.checkChunk context decode facts instructions 626688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_627200 : Path.checkChunk context decode facts instructions 627200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_627712 : Path.checkChunk context decode facts instructions 627712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_628224 : Path.checkChunk context decode facts instructions 628224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_628736 : Path.checkChunk context decode facts instructions 628736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_629248 : Path.checkChunk context decode facts instructions 629248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_629760 : Path.checkChunk context decode facts instructions 629760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_630272 : Path.checkChunk context decode facts instructions 630272 512 = true := by
  decide +kernel

theorem sound_622592 (prior : ∀ n, n < 622592 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 630784 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h623104 := Path.chunk_sound context_valid decode facts instructions 622592 512
    prior checked_622592
  have h623616 := Path.chunk_sound context_valid decode facts instructions 623104 512
    h623104 checked_623104
  have h624128 := Path.chunk_sound context_valid decode facts instructions 623616 512
    h623616 checked_623616
  have h624640 := Path.chunk_sound context_valid decode facts instructions 624128 512
    h624128 checked_624128
  have h625152 := Path.chunk_sound context_valid decode facts instructions 624640 512
    h624640 checked_624640
  have h625664 := Path.chunk_sound context_valid decode facts instructions 625152 512
    h625152 checked_625152
  have h626176 := Path.chunk_sound context_valid decode facts instructions 625664 512
    h625664 checked_625664
  have h626688 := Path.chunk_sound context_valid decode facts instructions 626176 512
    h626176 checked_626176
  have h627200 := Path.chunk_sound context_valid decode facts instructions 626688 512
    h626688 checked_626688
  have h627712 := Path.chunk_sound context_valid decode facts instructions 627200 512
    h627200 checked_627200
  have h628224 := Path.chunk_sound context_valid decode facts instructions 627712 512
    h627712 checked_627712
  have h628736 := Path.chunk_sound context_valid decode facts instructions 628224 512
    h628224 checked_628224
  have h629248 := Path.chunk_sound context_valid decode facts instructions 628736 512
    h628736 checked_628736
  have h629760 := Path.chunk_sound context_valid decode facts instructions 629248 512
    h629248 checked_629248
  have h630272 := Path.chunk_sound context_valid decode facts instructions 629760 512
    h629760 checked_629760
  have h630784 := Path.chunk_sound context_valid decode facts instructions 630272 512
    h630272 checked_630272
  exact h630784

end Sporadic.Janko3.AmalgamPresentation.Cover
