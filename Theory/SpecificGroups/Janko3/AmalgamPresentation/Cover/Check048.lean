module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_393216 : Path.checkChunk context decode facts instructions 393216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_393728 : Path.checkChunk context decode facts instructions 393728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_394240 : Path.checkChunk context decode facts instructions 394240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_394752 : Path.checkChunk context decode facts instructions 394752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_395264 : Path.checkChunk context decode facts instructions 395264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_395776 : Path.checkChunk context decode facts instructions 395776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_396288 : Path.checkChunk context decode facts instructions 396288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_396800 : Path.checkChunk context decode facts instructions 396800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_397312 : Path.checkChunk context decode facts instructions 397312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_397824 : Path.checkChunk context decode facts instructions 397824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_398336 : Path.checkChunk context decode facts instructions 398336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_398848 : Path.checkChunk context decode facts instructions 398848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_399360 : Path.checkChunk context decode facts instructions 399360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_399872 : Path.checkChunk context decode facts instructions 399872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_400384 : Path.checkChunk context decode facts instructions 400384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_400896 : Path.checkChunk context decode facts instructions 400896 512 = true := by
  decide +kernel

theorem sound_393216 (prior : ∀ n, n < 393216 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 401408 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h393728 := Path.chunk_sound context_valid decode facts instructions 393216 512
    prior checked_393216
  have h394240 := Path.chunk_sound context_valid decode facts instructions 393728 512
    h393728 checked_393728
  have h394752 := Path.chunk_sound context_valid decode facts instructions 394240 512
    h394240 checked_394240
  have h395264 := Path.chunk_sound context_valid decode facts instructions 394752 512
    h394752 checked_394752
  have h395776 := Path.chunk_sound context_valid decode facts instructions 395264 512
    h395264 checked_395264
  have h396288 := Path.chunk_sound context_valid decode facts instructions 395776 512
    h395776 checked_395776
  have h396800 := Path.chunk_sound context_valid decode facts instructions 396288 512
    h396288 checked_396288
  have h397312 := Path.chunk_sound context_valid decode facts instructions 396800 512
    h396800 checked_396800
  have h397824 := Path.chunk_sound context_valid decode facts instructions 397312 512
    h397312 checked_397312
  have h398336 := Path.chunk_sound context_valid decode facts instructions 397824 512
    h397824 checked_397824
  have h398848 := Path.chunk_sound context_valid decode facts instructions 398336 512
    h398336 checked_398336
  have h399360 := Path.chunk_sound context_valid decode facts instructions 398848 512
    h398848 checked_398848
  have h399872 := Path.chunk_sound context_valid decode facts instructions 399360 512
    h399360 checked_399360
  have h400384 := Path.chunk_sound context_valid decode facts instructions 399872 512
    h399872 checked_399872
  have h400896 := Path.chunk_sound context_valid decode facts instructions 400384 512
    h400384 checked_400384
  have h401408 := Path.chunk_sound context_valid decode facts instructions 400896 512
    h400896 checked_400896
  exact h401408

end Sporadic.Janko3.AmalgamPresentation.Cover
