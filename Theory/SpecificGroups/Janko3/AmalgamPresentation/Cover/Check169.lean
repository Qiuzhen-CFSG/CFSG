module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1384448 : Path.checkChunk context decode facts instructions 1384448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1384960 : Path.checkChunk context decode facts instructions 1384960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1385472 : Path.checkChunk context decode facts instructions 1385472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1385984 : Path.checkChunk context decode facts instructions 1385984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1386496 : Path.checkChunk context decode facts instructions 1386496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1387008 : Path.checkChunk context decode facts instructions 1387008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1387520 : Path.checkChunk context decode facts instructions 1387520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1388032 : Path.checkChunk context decode facts instructions 1388032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1388544 : Path.checkChunk context decode facts instructions 1388544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1389056 : Path.checkChunk context decode facts instructions 1389056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1389568 : Path.checkChunk context decode facts instructions 1389568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1390080 : Path.checkChunk context decode facts instructions 1390080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1390592 : Path.checkChunk context decode facts instructions 1390592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1391104 : Path.checkChunk context decode facts instructions 1391104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1391616 : Path.checkChunk context decode facts instructions 1391616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1392128 : Path.checkChunk context decode facts instructions 1392128 512 = true := by
  decide +kernel

theorem sound_1384448 (prior : ∀ n, n < 1384448 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1392640 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1384960 := Path.chunk_sound context_valid decode facts instructions 1384448 512
    prior checked_1384448
  have h1385472 := Path.chunk_sound context_valid decode facts instructions 1384960 512
    h1384960 checked_1384960
  have h1385984 := Path.chunk_sound context_valid decode facts instructions 1385472 512
    h1385472 checked_1385472
  have h1386496 := Path.chunk_sound context_valid decode facts instructions 1385984 512
    h1385984 checked_1385984
  have h1387008 := Path.chunk_sound context_valid decode facts instructions 1386496 512
    h1386496 checked_1386496
  have h1387520 := Path.chunk_sound context_valid decode facts instructions 1387008 512
    h1387008 checked_1387008
  have h1388032 := Path.chunk_sound context_valid decode facts instructions 1387520 512
    h1387520 checked_1387520
  have h1388544 := Path.chunk_sound context_valid decode facts instructions 1388032 512
    h1388032 checked_1388032
  have h1389056 := Path.chunk_sound context_valid decode facts instructions 1388544 512
    h1388544 checked_1388544
  have h1389568 := Path.chunk_sound context_valid decode facts instructions 1389056 512
    h1389056 checked_1389056
  have h1390080 := Path.chunk_sound context_valid decode facts instructions 1389568 512
    h1389568 checked_1389568
  have h1390592 := Path.chunk_sound context_valid decode facts instructions 1390080 512
    h1390080 checked_1390080
  have h1391104 := Path.chunk_sound context_valid decode facts instructions 1390592 512
    h1390592 checked_1390592
  have h1391616 := Path.chunk_sound context_valid decode facts instructions 1391104 512
    h1391104 checked_1391104
  have h1392128 := Path.chunk_sound context_valid decode facts instructions 1391616 512
    h1391616 checked_1391616
  have h1392640 := Path.chunk_sound context_valid decode facts instructions 1392128 512
    h1392128 checked_1392128
  exact h1392640

end Sporadic.Janko3.AmalgamPresentation.Cover
