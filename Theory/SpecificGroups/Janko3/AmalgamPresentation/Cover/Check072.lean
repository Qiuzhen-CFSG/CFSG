module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_589824 : Path.checkChunk context decode facts instructions 589824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_590336 : Path.checkChunk context decode facts instructions 590336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_590848 : Path.checkChunk context decode facts instructions 590848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_591360 : Path.checkChunk context decode facts instructions 591360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_591872 : Path.checkChunk context decode facts instructions 591872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_592384 : Path.checkChunk context decode facts instructions 592384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_592896 : Path.checkChunk context decode facts instructions 592896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_593408 : Path.checkChunk context decode facts instructions 593408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_593920 : Path.checkChunk context decode facts instructions 593920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_594432 : Path.checkChunk context decode facts instructions 594432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_594944 : Path.checkChunk context decode facts instructions 594944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_595456 : Path.checkChunk context decode facts instructions 595456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_595968 : Path.checkChunk context decode facts instructions 595968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_596480 : Path.checkChunk context decode facts instructions 596480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_596992 : Path.checkChunk context decode facts instructions 596992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_597504 : Path.checkChunk context decode facts instructions 597504 512 = true := by
  decide +kernel

theorem sound_589824 (prior : ∀ n, n < 589824 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 598016 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h590336 := Path.chunk_sound context_valid decode facts instructions 589824 512
    prior checked_589824
  have h590848 := Path.chunk_sound context_valid decode facts instructions 590336 512
    h590336 checked_590336
  have h591360 := Path.chunk_sound context_valid decode facts instructions 590848 512
    h590848 checked_590848
  have h591872 := Path.chunk_sound context_valid decode facts instructions 591360 512
    h591360 checked_591360
  have h592384 := Path.chunk_sound context_valid decode facts instructions 591872 512
    h591872 checked_591872
  have h592896 := Path.chunk_sound context_valid decode facts instructions 592384 512
    h592384 checked_592384
  have h593408 := Path.chunk_sound context_valid decode facts instructions 592896 512
    h592896 checked_592896
  have h593920 := Path.chunk_sound context_valid decode facts instructions 593408 512
    h593408 checked_593408
  have h594432 := Path.chunk_sound context_valid decode facts instructions 593920 512
    h593920 checked_593920
  have h594944 := Path.chunk_sound context_valid decode facts instructions 594432 512
    h594432 checked_594432
  have h595456 := Path.chunk_sound context_valid decode facts instructions 594944 512
    h594944 checked_594944
  have h595968 := Path.chunk_sound context_valid decode facts instructions 595456 512
    h595456 checked_595456
  have h596480 := Path.chunk_sound context_valid decode facts instructions 595968 512
    h595968 checked_595968
  have h596992 := Path.chunk_sound context_valid decode facts instructions 596480 512
    h596480 checked_596480
  have h597504 := Path.chunk_sound context_valid decode facts instructions 596992 512
    h596992 checked_596992
  have h598016 := Path.chunk_sound context_valid decode facts instructions 597504 512
    h597504 checked_597504
  exact h598016

end Sporadic.Janko3.AmalgamPresentation.Cover
