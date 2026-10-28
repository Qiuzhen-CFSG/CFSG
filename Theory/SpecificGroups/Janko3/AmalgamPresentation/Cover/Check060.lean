module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_491520 : Path.checkChunk context decode facts instructions 491520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_492032 : Path.checkChunk context decode facts instructions 492032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_492544 : Path.checkChunk context decode facts instructions 492544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_493056 : Path.checkChunk context decode facts instructions 493056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_493568 : Path.checkChunk context decode facts instructions 493568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_494080 : Path.checkChunk context decode facts instructions 494080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_494592 : Path.checkChunk context decode facts instructions 494592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_495104 : Path.checkChunk context decode facts instructions 495104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_495616 : Path.checkChunk context decode facts instructions 495616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_496128 : Path.checkChunk context decode facts instructions 496128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_496640 : Path.checkChunk context decode facts instructions 496640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_497152 : Path.checkChunk context decode facts instructions 497152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_497664 : Path.checkChunk context decode facts instructions 497664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_498176 : Path.checkChunk context decode facts instructions 498176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_498688 : Path.checkChunk context decode facts instructions 498688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_499200 : Path.checkChunk context decode facts instructions 499200 512 = true := by
  decide +kernel

theorem sound_491520 (prior : ∀ n, n < 491520 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 499712 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h492032 := Path.chunk_sound context_valid decode facts instructions 491520 512
    prior checked_491520
  have h492544 := Path.chunk_sound context_valid decode facts instructions 492032 512
    h492032 checked_492032
  have h493056 := Path.chunk_sound context_valid decode facts instructions 492544 512
    h492544 checked_492544
  have h493568 := Path.chunk_sound context_valid decode facts instructions 493056 512
    h493056 checked_493056
  have h494080 := Path.chunk_sound context_valid decode facts instructions 493568 512
    h493568 checked_493568
  have h494592 := Path.chunk_sound context_valid decode facts instructions 494080 512
    h494080 checked_494080
  have h495104 := Path.chunk_sound context_valid decode facts instructions 494592 512
    h494592 checked_494592
  have h495616 := Path.chunk_sound context_valid decode facts instructions 495104 512
    h495104 checked_495104
  have h496128 := Path.chunk_sound context_valid decode facts instructions 495616 512
    h495616 checked_495616
  have h496640 := Path.chunk_sound context_valid decode facts instructions 496128 512
    h496128 checked_496128
  have h497152 := Path.chunk_sound context_valid decode facts instructions 496640 512
    h496640 checked_496640
  have h497664 := Path.chunk_sound context_valid decode facts instructions 497152 512
    h497152 checked_497152
  have h498176 := Path.chunk_sound context_valid decode facts instructions 497664 512
    h497664 checked_497664
  have h498688 := Path.chunk_sound context_valid decode facts instructions 498176 512
    h498176 checked_498176
  have h499200 := Path.chunk_sound context_valid decode facts instructions 498688 512
    h498688 checked_498688
  have h499712 := Path.chunk_sound context_valid decode facts instructions 499200 512
    h499200 checked_499200
  exact h499712

end Sporadic.Janko3.AmalgamPresentation.Cover
