module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_933888 : Path.checkChunk context decode facts instructions 933888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_934400 : Path.checkChunk context decode facts instructions 934400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_934912 : Path.checkChunk context decode facts instructions 934912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_935424 : Path.checkChunk context decode facts instructions 935424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_935936 : Path.checkChunk context decode facts instructions 935936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_936448 : Path.checkChunk context decode facts instructions 936448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_936960 : Path.checkChunk context decode facts instructions 936960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_937472 : Path.checkChunk context decode facts instructions 937472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_937984 : Path.checkChunk context decode facts instructions 937984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_938496 : Path.checkChunk context decode facts instructions 938496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_939008 : Path.checkChunk context decode facts instructions 939008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_939520 : Path.checkChunk context decode facts instructions 939520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_940032 : Path.checkChunk context decode facts instructions 940032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_940544 : Path.checkChunk context decode facts instructions 940544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_941056 : Path.checkChunk context decode facts instructions 941056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_941568 : Path.checkChunk context decode facts instructions 941568 512 = true := by
  decide +kernel

theorem sound_933888 (prior : ∀ n, n < 933888 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 942080 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h934400 := Path.chunk_sound context_valid decode facts instructions 933888 512
    prior checked_933888
  have h934912 := Path.chunk_sound context_valid decode facts instructions 934400 512
    h934400 checked_934400
  have h935424 := Path.chunk_sound context_valid decode facts instructions 934912 512
    h934912 checked_934912
  have h935936 := Path.chunk_sound context_valid decode facts instructions 935424 512
    h935424 checked_935424
  have h936448 := Path.chunk_sound context_valid decode facts instructions 935936 512
    h935936 checked_935936
  have h936960 := Path.chunk_sound context_valid decode facts instructions 936448 512
    h936448 checked_936448
  have h937472 := Path.chunk_sound context_valid decode facts instructions 936960 512
    h936960 checked_936960
  have h937984 := Path.chunk_sound context_valid decode facts instructions 937472 512
    h937472 checked_937472
  have h938496 := Path.chunk_sound context_valid decode facts instructions 937984 512
    h937984 checked_937984
  have h939008 := Path.chunk_sound context_valid decode facts instructions 938496 512
    h938496 checked_938496
  have h939520 := Path.chunk_sound context_valid decode facts instructions 939008 512
    h939008 checked_939008
  have h940032 := Path.chunk_sound context_valid decode facts instructions 939520 512
    h939520 checked_939520
  have h940544 := Path.chunk_sound context_valid decode facts instructions 940032 512
    h940032 checked_940032
  have h941056 := Path.chunk_sound context_valid decode facts instructions 940544 512
    h940544 checked_940544
  have h941568 := Path.chunk_sound context_valid decode facts instructions 941056 512
    h941056 checked_941056
  have h942080 := Path.chunk_sound context_valid decode facts instructions 941568 512
    h941568 checked_941568
  exact h942080

end Sporadic.Janko3.AmalgamPresentation.Cover
