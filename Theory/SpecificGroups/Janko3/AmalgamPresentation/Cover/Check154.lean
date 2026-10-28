module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1261568 : Path.checkChunk context decode facts instructions 1261568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1262080 : Path.checkChunk context decode facts instructions 1262080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1262592 : Path.checkChunk context decode facts instructions 1262592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1263104 : Path.checkChunk context decode facts instructions 1263104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1263616 : Path.checkChunk context decode facts instructions 1263616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1264128 : Path.checkChunk context decode facts instructions 1264128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1264640 : Path.checkChunk context decode facts instructions 1264640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1265152 : Path.checkChunk context decode facts instructions 1265152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1265664 : Path.checkChunk context decode facts instructions 1265664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1266176 : Path.checkChunk context decode facts instructions 1266176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1266688 : Path.checkChunk context decode facts instructions 1266688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1267200 : Path.checkChunk context decode facts instructions 1267200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1267712 : Path.checkChunk context decode facts instructions 1267712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1268224 : Path.checkChunk context decode facts instructions 1268224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1268736 : Path.checkChunk context decode facts instructions 1268736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1269248 : Path.checkChunk context decode facts instructions 1269248 512 = true := by
  decide +kernel

theorem sound_1261568 (prior : ∀ n, n < 1261568 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1269760 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1262080 := Path.chunk_sound context_valid decode facts instructions 1261568 512
    prior checked_1261568
  have h1262592 := Path.chunk_sound context_valid decode facts instructions 1262080 512
    h1262080 checked_1262080
  have h1263104 := Path.chunk_sound context_valid decode facts instructions 1262592 512
    h1262592 checked_1262592
  have h1263616 := Path.chunk_sound context_valid decode facts instructions 1263104 512
    h1263104 checked_1263104
  have h1264128 := Path.chunk_sound context_valid decode facts instructions 1263616 512
    h1263616 checked_1263616
  have h1264640 := Path.chunk_sound context_valid decode facts instructions 1264128 512
    h1264128 checked_1264128
  have h1265152 := Path.chunk_sound context_valid decode facts instructions 1264640 512
    h1264640 checked_1264640
  have h1265664 := Path.chunk_sound context_valid decode facts instructions 1265152 512
    h1265152 checked_1265152
  have h1266176 := Path.chunk_sound context_valid decode facts instructions 1265664 512
    h1265664 checked_1265664
  have h1266688 := Path.chunk_sound context_valid decode facts instructions 1266176 512
    h1266176 checked_1266176
  have h1267200 := Path.chunk_sound context_valid decode facts instructions 1266688 512
    h1266688 checked_1266688
  have h1267712 := Path.chunk_sound context_valid decode facts instructions 1267200 512
    h1267200 checked_1267200
  have h1268224 := Path.chunk_sound context_valid decode facts instructions 1267712 512
    h1267712 checked_1267712
  have h1268736 := Path.chunk_sound context_valid decode facts instructions 1268224 512
    h1268224 checked_1268224
  have h1269248 := Path.chunk_sound context_valid decode facts instructions 1268736 512
    h1268736 checked_1268736
  have h1269760 := Path.chunk_sound context_valid decode facts instructions 1269248 512
    h1269248 checked_1269248
  exact h1269760

end Sporadic.Janko3.AmalgamPresentation.Cover
