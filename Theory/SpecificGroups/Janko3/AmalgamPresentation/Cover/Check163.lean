module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1335296 : Path.checkChunk context decode facts instructions 1335296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1335808 : Path.checkChunk context decode facts instructions 1335808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1336320 : Path.checkChunk context decode facts instructions 1336320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1336832 : Path.checkChunk context decode facts instructions 1336832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1337344 : Path.checkChunk context decode facts instructions 1337344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1337856 : Path.checkChunk context decode facts instructions 1337856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1338368 : Path.checkChunk context decode facts instructions 1338368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1338880 : Path.checkChunk context decode facts instructions 1338880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1339392 : Path.checkChunk context decode facts instructions 1339392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1339904 : Path.checkChunk context decode facts instructions 1339904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1340416 : Path.checkChunk context decode facts instructions 1340416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1340928 : Path.checkChunk context decode facts instructions 1340928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1341440 : Path.checkChunk context decode facts instructions 1341440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1341952 : Path.checkChunk context decode facts instructions 1341952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1342464 : Path.checkChunk context decode facts instructions 1342464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1342976 : Path.checkChunk context decode facts instructions 1342976 512 = true := by
  decide +kernel

theorem sound_1335296 (prior : ∀ n, n < 1335296 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1343488 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1335808 := Path.chunk_sound context_valid decode facts instructions 1335296 512
    prior checked_1335296
  have h1336320 := Path.chunk_sound context_valid decode facts instructions 1335808 512
    h1335808 checked_1335808
  have h1336832 := Path.chunk_sound context_valid decode facts instructions 1336320 512
    h1336320 checked_1336320
  have h1337344 := Path.chunk_sound context_valid decode facts instructions 1336832 512
    h1336832 checked_1336832
  have h1337856 := Path.chunk_sound context_valid decode facts instructions 1337344 512
    h1337344 checked_1337344
  have h1338368 := Path.chunk_sound context_valid decode facts instructions 1337856 512
    h1337856 checked_1337856
  have h1338880 := Path.chunk_sound context_valid decode facts instructions 1338368 512
    h1338368 checked_1338368
  have h1339392 := Path.chunk_sound context_valid decode facts instructions 1338880 512
    h1338880 checked_1338880
  have h1339904 := Path.chunk_sound context_valid decode facts instructions 1339392 512
    h1339392 checked_1339392
  have h1340416 := Path.chunk_sound context_valid decode facts instructions 1339904 512
    h1339904 checked_1339904
  have h1340928 := Path.chunk_sound context_valid decode facts instructions 1340416 512
    h1340416 checked_1340416
  have h1341440 := Path.chunk_sound context_valid decode facts instructions 1340928 512
    h1340928 checked_1340928
  have h1341952 := Path.chunk_sound context_valid decode facts instructions 1341440 512
    h1341440 checked_1341440
  have h1342464 := Path.chunk_sound context_valid decode facts instructions 1341952 512
    h1341952 checked_1341952
  have h1342976 := Path.chunk_sound context_valid decode facts instructions 1342464 512
    h1342464 checked_1342464
  have h1343488 := Path.chunk_sound context_valid decode facts instructions 1342976 512
    h1342976 checked_1342976
  exact h1343488

end Sporadic.Janko3.AmalgamPresentation.Cover
