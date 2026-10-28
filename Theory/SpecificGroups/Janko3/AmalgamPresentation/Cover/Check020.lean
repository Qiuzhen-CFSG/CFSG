module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_163840 : Path.checkChunk context decode facts instructions 163840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_164352 : Path.checkChunk context decode facts instructions 164352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_164864 : Path.checkChunk context decode facts instructions 164864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_165376 : Path.checkChunk context decode facts instructions 165376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_165888 : Path.checkChunk context decode facts instructions 165888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_166400 : Path.checkChunk context decode facts instructions 166400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_166912 : Path.checkChunk context decode facts instructions 166912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_167424 : Path.checkChunk context decode facts instructions 167424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_167936 : Path.checkChunk context decode facts instructions 167936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_168448 : Path.checkChunk context decode facts instructions 168448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_168960 : Path.checkChunk context decode facts instructions 168960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_169472 : Path.checkChunk context decode facts instructions 169472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_169984 : Path.checkChunk context decode facts instructions 169984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_170496 : Path.checkChunk context decode facts instructions 170496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_171008 : Path.checkChunk context decode facts instructions 171008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_171520 : Path.checkChunk context decode facts instructions 171520 512 = true := by
  decide +kernel

theorem sound_163840 (prior : ∀ n, n < 163840 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 172032 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h164352 := Path.chunk_sound context_valid decode facts instructions 163840 512
    prior checked_163840
  have h164864 := Path.chunk_sound context_valid decode facts instructions 164352 512
    h164352 checked_164352
  have h165376 := Path.chunk_sound context_valid decode facts instructions 164864 512
    h164864 checked_164864
  have h165888 := Path.chunk_sound context_valid decode facts instructions 165376 512
    h165376 checked_165376
  have h166400 := Path.chunk_sound context_valid decode facts instructions 165888 512
    h165888 checked_165888
  have h166912 := Path.chunk_sound context_valid decode facts instructions 166400 512
    h166400 checked_166400
  have h167424 := Path.chunk_sound context_valid decode facts instructions 166912 512
    h166912 checked_166912
  have h167936 := Path.chunk_sound context_valid decode facts instructions 167424 512
    h167424 checked_167424
  have h168448 := Path.chunk_sound context_valid decode facts instructions 167936 512
    h167936 checked_167936
  have h168960 := Path.chunk_sound context_valid decode facts instructions 168448 512
    h168448 checked_168448
  have h169472 := Path.chunk_sound context_valid decode facts instructions 168960 512
    h168960 checked_168960
  have h169984 := Path.chunk_sound context_valid decode facts instructions 169472 512
    h169472 checked_169472
  have h170496 := Path.chunk_sound context_valid decode facts instructions 169984 512
    h169984 checked_169984
  have h171008 := Path.chunk_sound context_valid decode facts instructions 170496 512
    h170496 checked_170496
  have h171520 := Path.chunk_sound context_valid decode facts instructions 171008 512
    h171008 checked_171008
  have h172032 := Path.chunk_sound context_valid decode facts instructions 171520 512
    h171520 checked_171520
  exact h172032

end Sporadic.Janko3.AmalgamPresentation.Cover
