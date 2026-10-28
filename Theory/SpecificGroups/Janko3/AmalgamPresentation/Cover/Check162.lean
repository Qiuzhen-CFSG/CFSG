module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1327104 : Path.checkChunk context decode facts instructions 1327104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1327616 : Path.checkChunk context decode facts instructions 1327616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1328128 : Path.checkChunk context decode facts instructions 1328128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1328640 : Path.checkChunk context decode facts instructions 1328640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1329152 : Path.checkChunk context decode facts instructions 1329152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1329664 : Path.checkChunk context decode facts instructions 1329664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1330176 : Path.checkChunk context decode facts instructions 1330176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1330688 : Path.checkChunk context decode facts instructions 1330688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1331200 : Path.checkChunk context decode facts instructions 1331200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1331712 : Path.checkChunk context decode facts instructions 1331712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1332224 : Path.checkChunk context decode facts instructions 1332224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1332736 : Path.checkChunk context decode facts instructions 1332736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1333248 : Path.checkChunk context decode facts instructions 1333248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1333760 : Path.checkChunk context decode facts instructions 1333760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1334272 : Path.checkChunk context decode facts instructions 1334272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1334784 : Path.checkChunk context decode facts instructions 1334784 512 = true := by
  decide +kernel

theorem sound_1327104 (prior : ∀ n, n < 1327104 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1335296 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1327616 := Path.chunk_sound context_valid decode facts instructions 1327104 512
    prior checked_1327104
  have h1328128 := Path.chunk_sound context_valid decode facts instructions 1327616 512
    h1327616 checked_1327616
  have h1328640 := Path.chunk_sound context_valid decode facts instructions 1328128 512
    h1328128 checked_1328128
  have h1329152 := Path.chunk_sound context_valid decode facts instructions 1328640 512
    h1328640 checked_1328640
  have h1329664 := Path.chunk_sound context_valid decode facts instructions 1329152 512
    h1329152 checked_1329152
  have h1330176 := Path.chunk_sound context_valid decode facts instructions 1329664 512
    h1329664 checked_1329664
  have h1330688 := Path.chunk_sound context_valid decode facts instructions 1330176 512
    h1330176 checked_1330176
  have h1331200 := Path.chunk_sound context_valid decode facts instructions 1330688 512
    h1330688 checked_1330688
  have h1331712 := Path.chunk_sound context_valid decode facts instructions 1331200 512
    h1331200 checked_1331200
  have h1332224 := Path.chunk_sound context_valid decode facts instructions 1331712 512
    h1331712 checked_1331712
  have h1332736 := Path.chunk_sound context_valid decode facts instructions 1332224 512
    h1332224 checked_1332224
  have h1333248 := Path.chunk_sound context_valid decode facts instructions 1332736 512
    h1332736 checked_1332736
  have h1333760 := Path.chunk_sound context_valid decode facts instructions 1333248 512
    h1333248 checked_1333248
  have h1334272 := Path.chunk_sound context_valid decode facts instructions 1333760 512
    h1333760 checked_1333760
  have h1334784 := Path.chunk_sound context_valid decode facts instructions 1334272 512
    h1334272 checked_1334272
  have h1335296 := Path.chunk_sound context_valid decode facts instructions 1334784 512
    h1334784 checked_1334784
  exact h1335296

end Sporadic.Janko3.AmalgamPresentation.Cover
