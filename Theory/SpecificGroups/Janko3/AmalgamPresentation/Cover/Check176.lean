module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1441792 : Path.checkChunk context decode facts instructions 1441792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1442304 : Path.checkChunk context decode facts instructions 1442304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1442816 : Path.checkChunk context decode facts instructions 1442816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1443328 : Path.checkChunk context decode facts instructions 1443328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1443840 : Path.checkChunk context decode facts instructions 1443840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1444352 : Path.checkChunk context decode facts instructions 1444352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1444864 : Path.checkChunk context decode facts instructions 1444864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1445376 : Path.checkChunk context decode facts instructions 1445376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1445888 : Path.checkChunk context decode facts instructions 1445888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1446400 : Path.checkChunk context decode facts instructions 1446400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1446912 : Path.checkChunk context decode facts instructions 1446912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1447424 : Path.checkChunk context decode facts instructions 1447424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1447936 : Path.checkChunk context decode facts instructions 1447936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1448448 : Path.checkChunk context decode facts instructions 1448448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1448960 : Path.checkChunk context decode facts instructions 1448960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1449472 : Path.checkChunk context decode facts instructions 1449472 512 = true := by
  decide +kernel

theorem sound_1441792 (prior : ∀ n, n < 1441792 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1449984 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1442304 := Path.chunk_sound context_valid decode facts instructions 1441792 512
    prior checked_1441792
  have h1442816 := Path.chunk_sound context_valid decode facts instructions 1442304 512
    h1442304 checked_1442304
  have h1443328 := Path.chunk_sound context_valid decode facts instructions 1442816 512
    h1442816 checked_1442816
  have h1443840 := Path.chunk_sound context_valid decode facts instructions 1443328 512
    h1443328 checked_1443328
  have h1444352 := Path.chunk_sound context_valid decode facts instructions 1443840 512
    h1443840 checked_1443840
  have h1444864 := Path.chunk_sound context_valid decode facts instructions 1444352 512
    h1444352 checked_1444352
  have h1445376 := Path.chunk_sound context_valid decode facts instructions 1444864 512
    h1444864 checked_1444864
  have h1445888 := Path.chunk_sound context_valid decode facts instructions 1445376 512
    h1445376 checked_1445376
  have h1446400 := Path.chunk_sound context_valid decode facts instructions 1445888 512
    h1445888 checked_1445888
  have h1446912 := Path.chunk_sound context_valid decode facts instructions 1446400 512
    h1446400 checked_1446400
  have h1447424 := Path.chunk_sound context_valid decode facts instructions 1446912 512
    h1446912 checked_1446912
  have h1447936 := Path.chunk_sound context_valid decode facts instructions 1447424 512
    h1447424 checked_1447424
  have h1448448 := Path.chunk_sound context_valid decode facts instructions 1447936 512
    h1447936 checked_1447936
  have h1448960 := Path.chunk_sound context_valid decode facts instructions 1448448 512
    h1448448 checked_1448448
  have h1449472 := Path.chunk_sound context_valid decode facts instructions 1448960 512
    h1448960 checked_1448960
  have h1449984 := Path.chunk_sound context_valid decode facts instructions 1449472 512
    h1449472 checked_1449472
  exact h1449984

end Sporadic.Janko3.AmalgamPresentation.Cover
