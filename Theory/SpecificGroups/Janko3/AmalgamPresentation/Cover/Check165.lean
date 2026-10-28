module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1351680 : Path.checkChunk context decode facts instructions 1351680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1352192 : Path.checkChunk context decode facts instructions 1352192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1352704 : Path.checkChunk context decode facts instructions 1352704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1353216 : Path.checkChunk context decode facts instructions 1353216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1353728 : Path.checkChunk context decode facts instructions 1353728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1354240 : Path.checkChunk context decode facts instructions 1354240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1354752 : Path.checkChunk context decode facts instructions 1354752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1355264 : Path.checkChunk context decode facts instructions 1355264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1355776 : Path.checkChunk context decode facts instructions 1355776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1356288 : Path.checkChunk context decode facts instructions 1356288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1356800 : Path.checkChunk context decode facts instructions 1356800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1357312 : Path.checkChunk context decode facts instructions 1357312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1357824 : Path.checkChunk context decode facts instructions 1357824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1358336 : Path.checkChunk context decode facts instructions 1358336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1358848 : Path.checkChunk context decode facts instructions 1358848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1359360 : Path.checkChunk context decode facts instructions 1359360 512 = true := by
  decide +kernel

theorem sound_1351680 (prior : ∀ n, n < 1351680 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1359872 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1352192 := Path.chunk_sound context_valid decode facts instructions 1351680 512
    prior checked_1351680
  have h1352704 := Path.chunk_sound context_valid decode facts instructions 1352192 512
    h1352192 checked_1352192
  have h1353216 := Path.chunk_sound context_valid decode facts instructions 1352704 512
    h1352704 checked_1352704
  have h1353728 := Path.chunk_sound context_valid decode facts instructions 1353216 512
    h1353216 checked_1353216
  have h1354240 := Path.chunk_sound context_valid decode facts instructions 1353728 512
    h1353728 checked_1353728
  have h1354752 := Path.chunk_sound context_valid decode facts instructions 1354240 512
    h1354240 checked_1354240
  have h1355264 := Path.chunk_sound context_valid decode facts instructions 1354752 512
    h1354752 checked_1354752
  have h1355776 := Path.chunk_sound context_valid decode facts instructions 1355264 512
    h1355264 checked_1355264
  have h1356288 := Path.chunk_sound context_valid decode facts instructions 1355776 512
    h1355776 checked_1355776
  have h1356800 := Path.chunk_sound context_valid decode facts instructions 1356288 512
    h1356288 checked_1356288
  have h1357312 := Path.chunk_sound context_valid decode facts instructions 1356800 512
    h1356800 checked_1356800
  have h1357824 := Path.chunk_sound context_valid decode facts instructions 1357312 512
    h1357312 checked_1357312
  have h1358336 := Path.chunk_sound context_valid decode facts instructions 1357824 512
    h1357824 checked_1357824
  have h1358848 := Path.chunk_sound context_valid decode facts instructions 1358336 512
    h1358336 checked_1358336
  have h1359360 := Path.chunk_sound context_valid decode facts instructions 1358848 512
    h1358848 checked_1358848
  have h1359872 := Path.chunk_sound context_valid decode facts instructions 1359360 512
    h1359360 checked_1359360
  exact h1359872

end Sporadic.Janko3.AmalgamPresentation.Cover
