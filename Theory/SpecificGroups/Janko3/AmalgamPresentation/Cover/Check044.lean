module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_360448 : Path.checkChunk context decode facts instructions 360448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_360960 : Path.checkChunk context decode facts instructions 360960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_361472 : Path.checkChunk context decode facts instructions 361472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_361984 : Path.checkChunk context decode facts instructions 361984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_362496 : Path.checkChunk context decode facts instructions 362496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_363008 : Path.checkChunk context decode facts instructions 363008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_363520 : Path.checkChunk context decode facts instructions 363520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_364032 : Path.checkChunk context decode facts instructions 364032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_364544 : Path.checkChunk context decode facts instructions 364544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_365056 : Path.checkChunk context decode facts instructions 365056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_365568 : Path.checkChunk context decode facts instructions 365568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_366080 : Path.checkChunk context decode facts instructions 366080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_366592 : Path.checkChunk context decode facts instructions 366592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_367104 : Path.checkChunk context decode facts instructions 367104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_367616 : Path.checkChunk context decode facts instructions 367616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_368128 : Path.checkChunk context decode facts instructions 368128 512 = true := by
  decide +kernel

theorem sound_360448 (prior : ∀ n, n < 360448 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 368640 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h360960 := Path.chunk_sound context_valid decode facts instructions 360448 512
    prior checked_360448
  have h361472 := Path.chunk_sound context_valid decode facts instructions 360960 512
    h360960 checked_360960
  have h361984 := Path.chunk_sound context_valid decode facts instructions 361472 512
    h361472 checked_361472
  have h362496 := Path.chunk_sound context_valid decode facts instructions 361984 512
    h361984 checked_361984
  have h363008 := Path.chunk_sound context_valid decode facts instructions 362496 512
    h362496 checked_362496
  have h363520 := Path.chunk_sound context_valid decode facts instructions 363008 512
    h363008 checked_363008
  have h364032 := Path.chunk_sound context_valid decode facts instructions 363520 512
    h363520 checked_363520
  have h364544 := Path.chunk_sound context_valid decode facts instructions 364032 512
    h364032 checked_364032
  have h365056 := Path.chunk_sound context_valid decode facts instructions 364544 512
    h364544 checked_364544
  have h365568 := Path.chunk_sound context_valid decode facts instructions 365056 512
    h365056 checked_365056
  have h366080 := Path.chunk_sound context_valid decode facts instructions 365568 512
    h365568 checked_365568
  have h366592 := Path.chunk_sound context_valid decode facts instructions 366080 512
    h366080 checked_366080
  have h367104 := Path.chunk_sound context_valid decode facts instructions 366592 512
    h366592 checked_366592
  have h367616 := Path.chunk_sound context_valid decode facts instructions 367104 512
    h367104 checked_367104
  have h368128 := Path.chunk_sound context_valid decode facts instructions 367616 512
    h367616 checked_367616
  have h368640 := Path.chunk_sound context_valid decode facts instructions 368128 512
    h368128 checked_368128
  exact h368640

end Sporadic.Janko3.AmalgamPresentation.Cover
