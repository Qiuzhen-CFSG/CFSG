module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1245184 : Path.checkChunk context decode facts instructions 1245184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1245696 : Path.checkChunk context decode facts instructions 1245696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1246208 : Path.checkChunk context decode facts instructions 1246208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1246720 : Path.checkChunk context decode facts instructions 1246720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1247232 : Path.checkChunk context decode facts instructions 1247232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1247744 : Path.checkChunk context decode facts instructions 1247744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1248256 : Path.checkChunk context decode facts instructions 1248256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1248768 : Path.checkChunk context decode facts instructions 1248768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1249280 : Path.checkChunk context decode facts instructions 1249280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1249792 : Path.checkChunk context decode facts instructions 1249792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1250304 : Path.checkChunk context decode facts instructions 1250304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1250816 : Path.checkChunk context decode facts instructions 1250816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1251328 : Path.checkChunk context decode facts instructions 1251328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1251840 : Path.checkChunk context decode facts instructions 1251840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1252352 : Path.checkChunk context decode facts instructions 1252352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1252864 : Path.checkChunk context decode facts instructions 1252864 512 = true := by
  decide +kernel

theorem sound_1245184 (prior : ∀ n, n < 1245184 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1253376 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1245696 := Path.chunk_sound context_valid decode facts instructions 1245184 512
    prior checked_1245184
  have h1246208 := Path.chunk_sound context_valid decode facts instructions 1245696 512
    h1245696 checked_1245696
  have h1246720 := Path.chunk_sound context_valid decode facts instructions 1246208 512
    h1246208 checked_1246208
  have h1247232 := Path.chunk_sound context_valid decode facts instructions 1246720 512
    h1246720 checked_1246720
  have h1247744 := Path.chunk_sound context_valid decode facts instructions 1247232 512
    h1247232 checked_1247232
  have h1248256 := Path.chunk_sound context_valid decode facts instructions 1247744 512
    h1247744 checked_1247744
  have h1248768 := Path.chunk_sound context_valid decode facts instructions 1248256 512
    h1248256 checked_1248256
  have h1249280 := Path.chunk_sound context_valid decode facts instructions 1248768 512
    h1248768 checked_1248768
  have h1249792 := Path.chunk_sound context_valid decode facts instructions 1249280 512
    h1249280 checked_1249280
  have h1250304 := Path.chunk_sound context_valid decode facts instructions 1249792 512
    h1249792 checked_1249792
  have h1250816 := Path.chunk_sound context_valid decode facts instructions 1250304 512
    h1250304 checked_1250304
  have h1251328 := Path.chunk_sound context_valid decode facts instructions 1250816 512
    h1250816 checked_1250816
  have h1251840 := Path.chunk_sound context_valid decode facts instructions 1251328 512
    h1251328 checked_1251328
  have h1252352 := Path.chunk_sound context_valid decode facts instructions 1251840 512
    h1251840 checked_1251840
  have h1252864 := Path.chunk_sound context_valid decode facts instructions 1252352 512
    h1252352 checked_1252352
  have h1253376 := Path.chunk_sound context_valid decode facts instructions 1252864 512
    h1252864 checked_1252864
  exact h1253376

end Sporadic.Janko3.AmalgamPresentation.Cover
