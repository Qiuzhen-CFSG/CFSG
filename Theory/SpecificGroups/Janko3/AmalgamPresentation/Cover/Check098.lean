module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_802816 : Path.checkChunk context decode facts instructions 802816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_803328 : Path.checkChunk context decode facts instructions 803328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_803840 : Path.checkChunk context decode facts instructions 803840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_804352 : Path.checkChunk context decode facts instructions 804352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_804864 : Path.checkChunk context decode facts instructions 804864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_805376 : Path.checkChunk context decode facts instructions 805376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_805888 : Path.checkChunk context decode facts instructions 805888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_806400 : Path.checkChunk context decode facts instructions 806400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_806912 : Path.checkChunk context decode facts instructions 806912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_807424 : Path.checkChunk context decode facts instructions 807424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_807936 : Path.checkChunk context decode facts instructions 807936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_808448 : Path.checkChunk context decode facts instructions 808448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_808960 : Path.checkChunk context decode facts instructions 808960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_809472 : Path.checkChunk context decode facts instructions 809472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_809984 : Path.checkChunk context decode facts instructions 809984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_810496 : Path.checkChunk context decode facts instructions 810496 512 = true := by
  decide +kernel

theorem sound_802816 (prior : ∀ n, n < 802816 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 811008 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h803328 := Path.chunk_sound context_valid decode facts instructions 802816 512
    prior checked_802816
  have h803840 := Path.chunk_sound context_valid decode facts instructions 803328 512
    h803328 checked_803328
  have h804352 := Path.chunk_sound context_valid decode facts instructions 803840 512
    h803840 checked_803840
  have h804864 := Path.chunk_sound context_valid decode facts instructions 804352 512
    h804352 checked_804352
  have h805376 := Path.chunk_sound context_valid decode facts instructions 804864 512
    h804864 checked_804864
  have h805888 := Path.chunk_sound context_valid decode facts instructions 805376 512
    h805376 checked_805376
  have h806400 := Path.chunk_sound context_valid decode facts instructions 805888 512
    h805888 checked_805888
  have h806912 := Path.chunk_sound context_valid decode facts instructions 806400 512
    h806400 checked_806400
  have h807424 := Path.chunk_sound context_valid decode facts instructions 806912 512
    h806912 checked_806912
  have h807936 := Path.chunk_sound context_valid decode facts instructions 807424 512
    h807424 checked_807424
  have h808448 := Path.chunk_sound context_valid decode facts instructions 807936 512
    h807936 checked_807936
  have h808960 := Path.chunk_sound context_valid decode facts instructions 808448 512
    h808448 checked_808448
  have h809472 := Path.chunk_sound context_valid decode facts instructions 808960 512
    h808960 checked_808960
  have h809984 := Path.chunk_sound context_valid decode facts instructions 809472 512
    h809472 checked_809472
  have h810496 := Path.chunk_sound context_valid decode facts instructions 809984 512
    h809984 checked_809984
  have h811008 := Path.chunk_sound context_valid decode facts instructions 810496 512
    h810496 checked_810496
  exact h811008

end Sporadic.Janko3.AmalgamPresentation.Cover
