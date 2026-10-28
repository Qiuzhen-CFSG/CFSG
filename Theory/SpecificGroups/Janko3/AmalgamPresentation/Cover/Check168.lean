module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1376256 : Path.checkChunk context decode facts instructions 1376256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1376768 : Path.checkChunk context decode facts instructions 1376768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1377280 : Path.checkChunk context decode facts instructions 1377280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1377792 : Path.checkChunk context decode facts instructions 1377792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1378304 : Path.checkChunk context decode facts instructions 1378304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1378816 : Path.checkChunk context decode facts instructions 1378816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1379328 : Path.checkChunk context decode facts instructions 1379328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1379840 : Path.checkChunk context decode facts instructions 1379840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1380352 : Path.checkChunk context decode facts instructions 1380352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1380864 : Path.checkChunk context decode facts instructions 1380864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1381376 : Path.checkChunk context decode facts instructions 1381376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1381888 : Path.checkChunk context decode facts instructions 1381888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1382400 : Path.checkChunk context decode facts instructions 1382400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1382912 : Path.checkChunk context decode facts instructions 1382912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1383424 : Path.checkChunk context decode facts instructions 1383424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1383936 : Path.checkChunk context decode facts instructions 1383936 512 = true := by
  decide +kernel

theorem sound_1376256 (prior : ∀ n, n < 1376256 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1384448 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1376768 := Path.chunk_sound context_valid decode facts instructions 1376256 512
    prior checked_1376256
  have h1377280 := Path.chunk_sound context_valid decode facts instructions 1376768 512
    h1376768 checked_1376768
  have h1377792 := Path.chunk_sound context_valid decode facts instructions 1377280 512
    h1377280 checked_1377280
  have h1378304 := Path.chunk_sound context_valid decode facts instructions 1377792 512
    h1377792 checked_1377792
  have h1378816 := Path.chunk_sound context_valid decode facts instructions 1378304 512
    h1378304 checked_1378304
  have h1379328 := Path.chunk_sound context_valid decode facts instructions 1378816 512
    h1378816 checked_1378816
  have h1379840 := Path.chunk_sound context_valid decode facts instructions 1379328 512
    h1379328 checked_1379328
  have h1380352 := Path.chunk_sound context_valid decode facts instructions 1379840 512
    h1379840 checked_1379840
  have h1380864 := Path.chunk_sound context_valid decode facts instructions 1380352 512
    h1380352 checked_1380352
  have h1381376 := Path.chunk_sound context_valid decode facts instructions 1380864 512
    h1380864 checked_1380864
  have h1381888 := Path.chunk_sound context_valid decode facts instructions 1381376 512
    h1381376 checked_1381376
  have h1382400 := Path.chunk_sound context_valid decode facts instructions 1381888 512
    h1381888 checked_1381888
  have h1382912 := Path.chunk_sound context_valid decode facts instructions 1382400 512
    h1382400 checked_1382400
  have h1383424 := Path.chunk_sound context_valid decode facts instructions 1382912 512
    h1382912 checked_1382912
  have h1383936 := Path.chunk_sound context_valid decode facts instructions 1383424 512
    h1383424 checked_1383424
  have h1384448 := Path.chunk_sound context_valid decode facts instructions 1383936 512
    h1383936 checked_1383936
  exact h1384448

end Sporadic.Janko3.AmalgamPresentation.Cover
