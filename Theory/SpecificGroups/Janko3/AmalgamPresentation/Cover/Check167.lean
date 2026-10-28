module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1368064 : Path.checkChunk context decode facts instructions 1368064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1368576 : Path.checkChunk context decode facts instructions 1368576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1369088 : Path.checkChunk context decode facts instructions 1369088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1369600 : Path.checkChunk context decode facts instructions 1369600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1370112 : Path.checkChunk context decode facts instructions 1370112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1370624 : Path.checkChunk context decode facts instructions 1370624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1371136 : Path.checkChunk context decode facts instructions 1371136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1371648 : Path.checkChunk context decode facts instructions 1371648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1372160 : Path.checkChunk context decode facts instructions 1372160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1372672 : Path.checkChunk context decode facts instructions 1372672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1373184 : Path.checkChunk context decode facts instructions 1373184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1373696 : Path.checkChunk context decode facts instructions 1373696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1374208 : Path.checkChunk context decode facts instructions 1374208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1374720 : Path.checkChunk context decode facts instructions 1374720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1375232 : Path.checkChunk context decode facts instructions 1375232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1375744 : Path.checkChunk context decode facts instructions 1375744 512 = true := by
  decide +kernel

theorem sound_1368064 (prior : ∀ n, n < 1368064 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1376256 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1368576 := Path.chunk_sound context_valid decode facts instructions 1368064 512
    prior checked_1368064
  have h1369088 := Path.chunk_sound context_valid decode facts instructions 1368576 512
    h1368576 checked_1368576
  have h1369600 := Path.chunk_sound context_valid decode facts instructions 1369088 512
    h1369088 checked_1369088
  have h1370112 := Path.chunk_sound context_valid decode facts instructions 1369600 512
    h1369600 checked_1369600
  have h1370624 := Path.chunk_sound context_valid decode facts instructions 1370112 512
    h1370112 checked_1370112
  have h1371136 := Path.chunk_sound context_valid decode facts instructions 1370624 512
    h1370624 checked_1370624
  have h1371648 := Path.chunk_sound context_valid decode facts instructions 1371136 512
    h1371136 checked_1371136
  have h1372160 := Path.chunk_sound context_valid decode facts instructions 1371648 512
    h1371648 checked_1371648
  have h1372672 := Path.chunk_sound context_valid decode facts instructions 1372160 512
    h1372160 checked_1372160
  have h1373184 := Path.chunk_sound context_valid decode facts instructions 1372672 512
    h1372672 checked_1372672
  have h1373696 := Path.chunk_sound context_valid decode facts instructions 1373184 512
    h1373184 checked_1373184
  have h1374208 := Path.chunk_sound context_valid decode facts instructions 1373696 512
    h1373696 checked_1373696
  have h1374720 := Path.chunk_sound context_valid decode facts instructions 1374208 512
    h1374208 checked_1374208
  have h1375232 := Path.chunk_sound context_valid decode facts instructions 1374720 512
    h1374720 checked_1374720
  have h1375744 := Path.chunk_sound context_valid decode facts instructions 1375232 512
    h1375232 checked_1375232
  have h1376256 := Path.chunk_sound context_valid decode facts instructions 1375744 512
    h1375744 checked_1375744
  exact h1376256

end Sporadic.Janko3.AmalgamPresentation.Cover
