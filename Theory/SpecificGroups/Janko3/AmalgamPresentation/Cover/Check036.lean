module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_294912 : Path.checkChunk context decode facts instructions 294912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_295424 : Path.checkChunk context decode facts instructions 295424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_295936 : Path.checkChunk context decode facts instructions 295936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_296448 : Path.checkChunk context decode facts instructions 296448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_296960 : Path.checkChunk context decode facts instructions 296960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_297472 : Path.checkChunk context decode facts instructions 297472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_297984 : Path.checkChunk context decode facts instructions 297984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_298496 : Path.checkChunk context decode facts instructions 298496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_299008 : Path.checkChunk context decode facts instructions 299008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_299520 : Path.checkChunk context decode facts instructions 299520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_300032 : Path.checkChunk context decode facts instructions 300032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_300544 : Path.checkChunk context decode facts instructions 300544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_301056 : Path.checkChunk context decode facts instructions 301056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_301568 : Path.checkChunk context decode facts instructions 301568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_302080 : Path.checkChunk context decode facts instructions 302080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_302592 : Path.checkChunk context decode facts instructions 302592 512 = true := by
  decide +kernel

theorem sound_294912 (prior : ∀ n, n < 294912 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 303104 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h295424 := Path.chunk_sound context_valid decode facts instructions 294912 512
    prior checked_294912
  have h295936 := Path.chunk_sound context_valid decode facts instructions 295424 512
    h295424 checked_295424
  have h296448 := Path.chunk_sound context_valid decode facts instructions 295936 512
    h295936 checked_295936
  have h296960 := Path.chunk_sound context_valid decode facts instructions 296448 512
    h296448 checked_296448
  have h297472 := Path.chunk_sound context_valid decode facts instructions 296960 512
    h296960 checked_296960
  have h297984 := Path.chunk_sound context_valid decode facts instructions 297472 512
    h297472 checked_297472
  have h298496 := Path.chunk_sound context_valid decode facts instructions 297984 512
    h297984 checked_297984
  have h299008 := Path.chunk_sound context_valid decode facts instructions 298496 512
    h298496 checked_298496
  have h299520 := Path.chunk_sound context_valid decode facts instructions 299008 512
    h299008 checked_299008
  have h300032 := Path.chunk_sound context_valid decode facts instructions 299520 512
    h299520 checked_299520
  have h300544 := Path.chunk_sound context_valid decode facts instructions 300032 512
    h300032 checked_300032
  have h301056 := Path.chunk_sound context_valid decode facts instructions 300544 512
    h300544 checked_300544
  have h301568 := Path.chunk_sound context_valid decode facts instructions 301056 512
    h301056 checked_301056
  have h302080 := Path.chunk_sound context_valid decode facts instructions 301568 512
    h301568 checked_301568
  have h302592 := Path.chunk_sound context_valid decode facts instructions 302080 512
    h302080 checked_302080
  have h303104 := Path.chunk_sound context_valid decode facts instructions 302592 512
    h302592 checked_302592
  exact h303104

end Sporadic.Janko3.AmalgamPresentation.Cover
