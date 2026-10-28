module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1204224 : Path.checkChunk context decode facts instructions 1204224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1204736 : Path.checkChunk context decode facts instructions 1204736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1205248 : Path.checkChunk context decode facts instructions 1205248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1205760 : Path.checkChunk context decode facts instructions 1205760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1206272 : Path.checkChunk context decode facts instructions 1206272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1206784 : Path.checkChunk context decode facts instructions 1206784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1207296 : Path.checkChunk context decode facts instructions 1207296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1207808 : Path.checkChunk context decode facts instructions 1207808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1208320 : Path.checkChunk context decode facts instructions 1208320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1208832 : Path.checkChunk context decode facts instructions 1208832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1209344 : Path.checkChunk context decode facts instructions 1209344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1209856 : Path.checkChunk context decode facts instructions 1209856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1210368 : Path.checkChunk context decode facts instructions 1210368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1210880 : Path.checkChunk context decode facts instructions 1210880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1211392 : Path.checkChunk context decode facts instructions 1211392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1211904 : Path.checkChunk context decode facts instructions 1211904 512 = true := by
  decide +kernel

theorem sound_1204224 (prior : ∀ n, n < 1204224 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1212416 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1204736 := Path.chunk_sound context_valid decode facts instructions 1204224 512
    prior checked_1204224
  have h1205248 := Path.chunk_sound context_valid decode facts instructions 1204736 512
    h1204736 checked_1204736
  have h1205760 := Path.chunk_sound context_valid decode facts instructions 1205248 512
    h1205248 checked_1205248
  have h1206272 := Path.chunk_sound context_valid decode facts instructions 1205760 512
    h1205760 checked_1205760
  have h1206784 := Path.chunk_sound context_valid decode facts instructions 1206272 512
    h1206272 checked_1206272
  have h1207296 := Path.chunk_sound context_valid decode facts instructions 1206784 512
    h1206784 checked_1206784
  have h1207808 := Path.chunk_sound context_valid decode facts instructions 1207296 512
    h1207296 checked_1207296
  have h1208320 := Path.chunk_sound context_valid decode facts instructions 1207808 512
    h1207808 checked_1207808
  have h1208832 := Path.chunk_sound context_valid decode facts instructions 1208320 512
    h1208320 checked_1208320
  have h1209344 := Path.chunk_sound context_valid decode facts instructions 1208832 512
    h1208832 checked_1208832
  have h1209856 := Path.chunk_sound context_valid decode facts instructions 1209344 512
    h1209344 checked_1209344
  have h1210368 := Path.chunk_sound context_valid decode facts instructions 1209856 512
    h1209856 checked_1209856
  have h1210880 := Path.chunk_sound context_valid decode facts instructions 1210368 512
    h1210368 checked_1210368
  have h1211392 := Path.chunk_sound context_valid decode facts instructions 1210880 512
    h1210880 checked_1210880
  have h1211904 := Path.chunk_sound context_valid decode facts instructions 1211392 512
    h1211392 checked_1211392
  have h1212416 := Path.chunk_sound context_valid decode facts instructions 1211904 512
    h1211904 checked_1211904
  exact h1212416

end Sporadic.Janko3.AmalgamPresentation.Cover
