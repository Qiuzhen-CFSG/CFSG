module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_876544 : Path.checkChunk context decode facts instructions 876544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_877056 : Path.checkChunk context decode facts instructions 877056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_877568 : Path.checkChunk context decode facts instructions 877568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_878080 : Path.checkChunk context decode facts instructions 878080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_878592 : Path.checkChunk context decode facts instructions 878592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_879104 : Path.checkChunk context decode facts instructions 879104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_879616 : Path.checkChunk context decode facts instructions 879616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_880128 : Path.checkChunk context decode facts instructions 880128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_880640 : Path.checkChunk context decode facts instructions 880640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_881152 : Path.checkChunk context decode facts instructions 881152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_881664 : Path.checkChunk context decode facts instructions 881664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_882176 : Path.checkChunk context decode facts instructions 882176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_882688 : Path.checkChunk context decode facts instructions 882688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_883200 : Path.checkChunk context decode facts instructions 883200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_883712 : Path.checkChunk context decode facts instructions 883712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_884224 : Path.checkChunk context decode facts instructions 884224 512 = true := by
  decide +kernel

theorem sound_876544 (prior : ∀ n, n < 876544 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 884736 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h877056 := Path.chunk_sound context_valid decode facts instructions 876544 512
    prior checked_876544
  have h877568 := Path.chunk_sound context_valid decode facts instructions 877056 512
    h877056 checked_877056
  have h878080 := Path.chunk_sound context_valid decode facts instructions 877568 512
    h877568 checked_877568
  have h878592 := Path.chunk_sound context_valid decode facts instructions 878080 512
    h878080 checked_878080
  have h879104 := Path.chunk_sound context_valid decode facts instructions 878592 512
    h878592 checked_878592
  have h879616 := Path.chunk_sound context_valid decode facts instructions 879104 512
    h879104 checked_879104
  have h880128 := Path.chunk_sound context_valid decode facts instructions 879616 512
    h879616 checked_879616
  have h880640 := Path.chunk_sound context_valid decode facts instructions 880128 512
    h880128 checked_880128
  have h881152 := Path.chunk_sound context_valid decode facts instructions 880640 512
    h880640 checked_880640
  have h881664 := Path.chunk_sound context_valid decode facts instructions 881152 512
    h881152 checked_881152
  have h882176 := Path.chunk_sound context_valid decode facts instructions 881664 512
    h881664 checked_881664
  have h882688 := Path.chunk_sound context_valid decode facts instructions 882176 512
    h882176 checked_882176
  have h883200 := Path.chunk_sound context_valid decode facts instructions 882688 512
    h882688 checked_882688
  have h883712 := Path.chunk_sound context_valid decode facts instructions 883200 512
    h883200 checked_883200
  have h884224 := Path.chunk_sound context_valid decode facts instructions 883712 512
    h883712 checked_883712
  have h884736 := Path.chunk_sound context_valid decode facts instructions 884224 512
    h884224 checked_884224
  exact h884736

end Sporadic.Janko3.AmalgamPresentation.Cover
