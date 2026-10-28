module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1359872 : Path.checkChunk context decode facts instructions 1359872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1360384 : Path.checkChunk context decode facts instructions 1360384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1360896 : Path.checkChunk context decode facts instructions 1360896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1361408 : Path.checkChunk context decode facts instructions 1361408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1361920 : Path.checkChunk context decode facts instructions 1361920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1362432 : Path.checkChunk context decode facts instructions 1362432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1362944 : Path.checkChunk context decode facts instructions 1362944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1363456 : Path.checkChunk context decode facts instructions 1363456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1363968 : Path.checkChunk context decode facts instructions 1363968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1364480 : Path.checkChunk context decode facts instructions 1364480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1364992 : Path.checkChunk context decode facts instructions 1364992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1365504 : Path.checkChunk context decode facts instructions 1365504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1366016 : Path.checkChunk context decode facts instructions 1366016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1366528 : Path.checkChunk context decode facts instructions 1366528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1367040 : Path.checkChunk context decode facts instructions 1367040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1367552 : Path.checkChunk context decode facts instructions 1367552 512 = true := by
  decide +kernel

theorem sound_1359872 (prior : ∀ n, n < 1359872 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1368064 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1360384 := Path.chunk_sound context_valid decode facts instructions 1359872 512
    prior checked_1359872
  have h1360896 := Path.chunk_sound context_valid decode facts instructions 1360384 512
    h1360384 checked_1360384
  have h1361408 := Path.chunk_sound context_valid decode facts instructions 1360896 512
    h1360896 checked_1360896
  have h1361920 := Path.chunk_sound context_valid decode facts instructions 1361408 512
    h1361408 checked_1361408
  have h1362432 := Path.chunk_sound context_valid decode facts instructions 1361920 512
    h1361920 checked_1361920
  have h1362944 := Path.chunk_sound context_valid decode facts instructions 1362432 512
    h1362432 checked_1362432
  have h1363456 := Path.chunk_sound context_valid decode facts instructions 1362944 512
    h1362944 checked_1362944
  have h1363968 := Path.chunk_sound context_valid decode facts instructions 1363456 512
    h1363456 checked_1363456
  have h1364480 := Path.chunk_sound context_valid decode facts instructions 1363968 512
    h1363968 checked_1363968
  have h1364992 := Path.chunk_sound context_valid decode facts instructions 1364480 512
    h1364480 checked_1364480
  have h1365504 := Path.chunk_sound context_valid decode facts instructions 1364992 512
    h1364992 checked_1364992
  have h1366016 := Path.chunk_sound context_valid decode facts instructions 1365504 512
    h1365504 checked_1365504
  have h1366528 := Path.chunk_sound context_valid decode facts instructions 1366016 512
    h1366016 checked_1366016
  have h1367040 := Path.chunk_sound context_valid decode facts instructions 1366528 512
    h1366528 checked_1366528
  have h1367552 := Path.chunk_sound context_valid decode facts instructions 1367040 512
    h1367040 checked_1367040
  have h1368064 := Path.chunk_sound context_valid decode facts instructions 1367552 512
    h1367552 checked_1367552
  exact h1368064

end Sporadic.Janko3.AmalgamPresentation.Cover
