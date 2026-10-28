module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_745472 : Path.checkChunk context decode facts instructions 745472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_745984 : Path.checkChunk context decode facts instructions 745984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_746496 : Path.checkChunk context decode facts instructions 746496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_747008 : Path.checkChunk context decode facts instructions 747008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_747520 : Path.checkChunk context decode facts instructions 747520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_748032 : Path.checkChunk context decode facts instructions 748032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_748544 : Path.checkChunk context decode facts instructions 748544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_749056 : Path.checkChunk context decode facts instructions 749056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_749568 : Path.checkChunk context decode facts instructions 749568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_750080 : Path.checkChunk context decode facts instructions 750080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_750592 : Path.checkChunk context decode facts instructions 750592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_751104 : Path.checkChunk context decode facts instructions 751104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_751616 : Path.checkChunk context decode facts instructions 751616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_752128 : Path.checkChunk context decode facts instructions 752128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_752640 : Path.checkChunk context decode facts instructions 752640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_753152 : Path.checkChunk context decode facts instructions 753152 512 = true := by
  decide +kernel

theorem sound_745472 (prior : ∀ n, n < 745472 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 753664 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h745984 := Path.chunk_sound context_valid decode facts instructions 745472 512
    prior checked_745472
  have h746496 := Path.chunk_sound context_valid decode facts instructions 745984 512
    h745984 checked_745984
  have h747008 := Path.chunk_sound context_valid decode facts instructions 746496 512
    h746496 checked_746496
  have h747520 := Path.chunk_sound context_valid decode facts instructions 747008 512
    h747008 checked_747008
  have h748032 := Path.chunk_sound context_valid decode facts instructions 747520 512
    h747520 checked_747520
  have h748544 := Path.chunk_sound context_valid decode facts instructions 748032 512
    h748032 checked_748032
  have h749056 := Path.chunk_sound context_valid decode facts instructions 748544 512
    h748544 checked_748544
  have h749568 := Path.chunk_sound context_valid decode facts instructions 749056 512
    h749056 checked_749056
  have h750080 := Path.chunk_sound context_valid decode facts instructions 749568 512
    h749568 checked_749568
  have h750592 := Path.chunk_sound context_valid decode facts instructions 750080 512
    h750080 checked_750080
  have h751104 := Path.chunk_sound context_valid decode facts instructions 750592 512
    h750592 checked_750592
  have h751616 := Path.chunk_sound context_valid decode facts instructions 751104 512
    h751104 checked_751104
  have h752128 := Path.chunk_sound context_valid decode facts instructions 751616 512
    h751616 checked_751616
  have h752640 := Path.chunk_sound context_valid decode facts instructions 752128 512
    h752128 checked_752128
  have h753152 := Path.chunk_sound context_valid decode facts instructions 752640 512
    h752640 checked_752640
  have h753664 := Path.chunk_sound context_valid decode facts instructions 753152 512
    h753152 checked_753152
  exact h753664

end Sporadic.Janko3.AmalgamPresentation.Cover
