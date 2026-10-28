module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_409600 : Path.checkChunk context decode facts instructions 409600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_410112 : Path.checkChunk context decode facts instructions 410112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_410624 : Path.checkChunk context decode facts instructions 410624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_411136 : Path.checkChunk context decode facts instructions 411136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_411648 : Path.checkChunk context decode facts instructions 411648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_412160 : Path.checkChunk context decode facts instructions 412160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_412672 : Path.checkChunk context decode facts instructions 412672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_413184 : Path.checkChunk context decode facts instructions 413184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_413696 : Path.checkChunk context decode facts instructions 413696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_414208 : Path.checkChunk context decode facts instructions 414208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_414720 : Path.checkChunk context decode facts instructions 414720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_415232 : Path.checkChunk context decode facts instructions 415232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_415744 : Path.checkChunk context decode facts instructions 415744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_416256 : Path.checkChunk context decode facts instructions 416256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_416768 : Path.checkChunk context decode facts instructions 416768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_417280 : Path.checkChunk context decode facts instructions 417280 512 = true := by
  decide +kernel

theorem sound_409600 (prior : ∀ n, n < 409600 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 417792 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h410112 := Path.chunk_sound context_valid decode facts instructions 409600 512
    prior checked_409600
  have h410624 := Path.chunk_sound context_valid decode facts instructions 410112 512
    h410112 checked_410112
  have h411136 := Path.chunk_sound context_valid decode facts instructions 410624 512
    h410624 checked_410624
  have h411648 := Path.chunk_sound context_valid decode facts instructions 411136 512
    h411136 checked_411136
  have h412160 := Path.chunk_sound context_valid decode facts instructions 411648 512
    h411648 checked_411648
  have h412672 := Path.chunk_sound context_valid decode facts instructions 412160 512
    h412160 checked_412160
  have h413184 := Path.chunk_sound context_valid decode facts instructions 412672 512
    h412672 checked_412672
  have h413696 := Path.chunk_sound context_valid decode facts instructions 413184 512
    h413184 checked_413184
  have h414208 := Path.chunk_sound context_valid decode facts instructions 413696 512
    h413696 checked_413696
  have h414720 := Path.chunk_sound context_valid decode facts instructions 414208 512
    h414208 checked_414208
  have h415232 := Path.chunk_sound context_valid decode facts instructions 414720 512
    h414720 checked_414720
  have h415744 := Path.chunk_sound context_valid decode facts instructions 415232 512
    h415232 checked_415232
  have h416256 := Path.chunk_sound context_valid decode facts instructions 415744 512
    h415744 checked_415744
  have h416768 := Path.chunk_sound context_valid decode facts instructions 416256 512
    h416256 checked_416256
  have h417280 := Path.chunk_sound context_valid decode facts instructions 416768 512
    h416768 checked_416768
  have h417792 := Path.chunk_sound context_valid decode facts instructions 417280 512
    h417280 checked_417280
  exact h417792

end Sporadic.Janko3.AmalgamPresentation.Cover
