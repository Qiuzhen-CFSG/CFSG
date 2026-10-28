module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1318912 : Path.checkChunk context decode facts instructions 1318912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1319424 : Path.checkChunk context decode facts instructions 1319424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1319936 : Path.checkChunk context decode facts instructions 1319936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1320448 : Path.checkChunk context decode facts instructions 1320448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1320960 : Path.checkChunk context decode facts instructions 1320960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1321472 : Path.checkChunk context decode facts instructions 1321472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1321984 : Path.checkChunk context decode facts instructions 1321984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1322496 : Path.checkChunk context decode facts instructions 1322496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1323008 : Path.checkChunk context decode facts instructions 1323008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1323520 : Path.checkChunk context decode facts instructions 1323520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1324032 : Path.checkChunk context decode facts instructions 1324032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1324544 : Path.checkChunk context decode facts instructions 1324544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1325056 : Path.checkChunk context decode facts instructions 1325056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1325568 : Path.checkChunk context decode facts instructions 1325568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1326080 : Path.checkChunk context decode facts instructions 1326080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1326592 : Path.checkChunk context decode facts instructions 1326592 512 = true := by
  decide +kernel

theorem sound_1318912 (prior : ∀ n, n < 1318912 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1327104 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1319424 := Path.chunk_sound context_valid decode facts instructions 1318912 512
    prior checked_1318912
  have h1319936 := Path.chunk_sound context_valid decode facts instructions 1319424 512
    h1319424 checked_1319424
  have h1320448 := Path.chunk_sound context_valid decode facts instructions 1319936 512
    h1319936 checked_1319936
  have h1320960 := Path.chunk_sound context_valid decode facts instructions 1320448 512
    h1320448 checked_1320448
  have h1321472 := Path.chunk_sound context_valid decode facts instructions 1320960 512
    h1320960 checked_1320960
  have h1321984 := Path.chunk_sound context_valid decode facts instructions 1321472 512
    h1321472 checked_1321472
  have h1322496 := Path.chunk_sound context_valid decode facts instructions 1321984 512
    h1321984 checked_1321984
  have h1323008 := Path.chunk_sound context_valid decode facts instructions 1322496 512
    h1322496 checked_1322496
  have h1323520 := Path.chunk_sound context_valid decode facts instructions 1323008 512
    h1323008 checked_1323008
  have h1324032 := Path.chunk_sound context_valid decode facts instructions 1323520 512
    h1323520 checked_1323520
  have h1324544 := Path.chunk_sound context_valid decode facts instructions 1324032 512
    h1324032 checked_1324032
  have h1325056 := Path.chunk_sound context_valid decode facts instructions 1324544 512
    h1324544 checked_1324544
  have h1325568 := Path.chunk_sound context_valid decode facts instructions 1325056 512
    h1325056 checked_1325056
  have h1326080 := Path.chunk_sound context_valid decode facts instructions 1325568 512
    h1325568 checked_1325568
  have h1326592 := Path.chunk_sound context_valid decode facts instructions 1326080 512
    h1326080 checked_1326080
  have h1327104 := Path.chunk_sound context_valid decode facts instructions 1326592 512
    h1326592 checked_1326592
  exact h1327104

end Sporadic.Janko3.AmalgamPresentation.Cover
