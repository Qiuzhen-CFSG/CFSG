module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1400832 : Path.checkChunk context decode facts instructions 1400832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1401344 : Path.checkChunk context decode facts instructions 1401344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1401856 : Path.checkChunk context decode facts instructions 1401856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1402368 : Path.checkChunk context decode facts instructions 1402368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1402880 : Path.checkChunk context decode facts instructions 1402880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1403392 : Path.checkChunk context decode facts instructions 1403392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1403904 : Path.checkChunk context decode facts instructions 1403904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1404416 : Path.checkChunk context decode facts instructions 1404416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1404928 : Path.checkChunk context decode facts instructions 1404928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1405440 : Path.checkChunk context decode facts instructions 1405440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1405952 : Path.checkChunk context decode facts instructions 1405952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1406464 : Path.checkChunk context decode facts instructions 1406464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1406976 : Path.checkChunk context decode facts instructions 1406976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1407488 : Path.checkChunk context decode facts instructions 1407488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1408000 : Path.checkChunk context decode facts instructions 1408000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1408512 : Path.checkChunk context decode facts instructions 1408512 512 = true := by
  decide +kernel

theorem sound_1400832 (prior : ∀ n, n < 1400832 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1409024 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1401344 := Path.chunk_sound context_valid decode facts instructions 1400832 512
    prior checked_1400832
  have h1401856 := Path.chunk_sound context_valid decode facts instructions 1401344 512
    h1401344 checked_1401344
  have h1402368 := Path.chunk_sound context_valid decode facts instructions 1401856 512
    h1401856 checked_1401856
  have h1402880 := Path.chunk_sound context_valid decode facts instructions 1402368 512
    h1402368 checked_1402368
  have h1403392 := Path.chunk_sound context_valid decode facts instructions 1402880 512
    h1402880 checked_1402880
  have h1403904 := Path.chunk_sound context_valid decode facts instructions 1403392 512
    h1403392 checked_1403392
  have h1404416 := Path.chunk_sound context_valid decode facts instructions 1403904 512
    h1403904 checked_1403904
  have h1404928 := Path.chunk_sound context_valid decode facts instructions 1404416 512
    h1404416 checked_1404416
  have h1405440 := Path.chunk_sound context_valid decode facts instructions 1404928 512
    h1404928 checked_1404928
  have h1405952 := Path.chunk_sound context_valid decode facts instructions 1405440 512
    h1405440 checked_1405440
  have h1406464 := Path.chunk_sound context_valid decode facts instructions 1405952 512
    h1405952 checked_1405952
  have h1406976 := Path.chunk_sound context_valid decode facts instructions 1406464 512
    h1406464 checked_1406464
  have h1407488 := Path.chunk_sound context_valid decode facts instructions 1406976 512
    h1406976 checked_1406976
  have h1408000 := Path.chunk_sound context_valid decode facts instructions 1407488 512
    h1407488 checked_1407488
  have h1408512 := Path.chunk_sound context_valid decode facts instructions 1408000 512
    h1408000 checked_1408000
  have h1409024 := Path.chunk_sound context_valid decode facts instructions 1408512 512
    h1408512 checked_1408512
  exact h1409024

end Sporadic.Janko3.AmalgamPresentation.Cover
