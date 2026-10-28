module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1417216 : Path.checkChunk context decode facts instructions 1417216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1417728 : Path.checkChunk context decode facts instructions 1417728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1418240 : Path.checkChunk context decode facts instructions 1418240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1418752 : Path.checkChunk context decode facts instructions 1418752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1419264 : Path.checkChunk context decode facts instructions 1419264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1419776 : Path.checkChunk context decode facts instructions 1419776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1420288 : Path.checkChunk context decode facts instructions 1420288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1420800 : Path.checkChunk context decode facts instructions 1420800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1421312 : Path.checkChunk context decode facts instructions 1421312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1421824 : Path.checkChunk context decode facts instructions 1421824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1422336 : Path.checkChunk context decode facts instructions 1422336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1422848 : Path.checkChunk context decode facts instructions 1422848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1423360 : Path.checkChunk context decode facts instructions 1423360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1423872 : Path.checkChunk context decode facts instructions 1423872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1424384 : Path.checkChunk context decode facts instructions 1424384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1424896 : Path.checkChunk context decode facts instructions 1424896 512 = true := by
  decide +kernel

theorem sound_1417216 (prior : ∀ n, n < 1417216 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1425408 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1417728 := Path.chunk_sound context_valid decode facts instructions 1417216 512
    prior checked_1417216
  have h1418240 := Path.chunk_sound context_valid decode facts instructions 1417728 512
    h1417728 checked_1417728
  have h1418752 := Path.chunk_sound context_valid decode facts instructions 1418240 512
    h1418240 checked_1418240
  have h1419264 := Path.chunk_sound context_valid decode facts instructions 1418752 512
    h1418752 checked_1418752
  have h1419776 := Path.chunk_sound context_valid decode facts instructions 1419264 512
    h1419264 checked_1419264
  have h1420288 := Path.chunk_sound context_valid decode facts instructions 1419776 512
    h1419776 checked_1419776
  have h1420800 := Path.chunk_sound context_valid decode facts instructions 1420288 512
    h1420288 checked_1420288
  have h1421312 := Path.chunk_sound context_valid decode facts instructions 1420800 512
    h1420800 checked_1420800
  have h1421824 := Path.chunk_sound context_valid decode facts instructions 1421312 512
    h1421312 checked_1421312
  have h1422336 := Path.chunk_sound context_valid decode facts instructions 1421824 512
    h1421824 checked_1421824
  have h1422848 := Path.chunk_sound context_valid decode facts instructions 1422336 512
    h1422336 checked_1422336
  have h1423360 := Path.chunk_sound context_valid decode facts instructions 1422848 512
    h1422848 checked_1422848
  have h1423872 := Path.chunk_sound context_valid decode facts instructions 1423360 512
    h1423360 checked_1423360
  have h1424384 := Path.chunk_sound context_valid decode facts instructions 1423872 512
    h1423872 checked_1423872
  have h1424896 := Path.chunk_sound context_valid decode facts instructions 1424384 512
    h1424384 checked_1424384
  have h1425408 := Path.chunk_sound context_valid decode facts instructions 1424896 512
    h1424896 checked_1424896
  exact h1425408

end Sporadic.Janko3.AmalgamPresentation.Cover
