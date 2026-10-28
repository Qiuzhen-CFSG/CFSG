module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_655360 : Path.checkChunk context decode facts instructions 655360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_655872 : Path.checkChunk context decode facts instructions 655872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_656384 : Path.checkChunk context decode facts instructions 656384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_656896 : Path.checkChunk context decode facts instructions 656896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_657408 : Path.checkChunk context decode facts instructions 657408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_657920 : Path.checkChunk context decode facts instructions 657920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_658432 : Path.checkChunk context decode facts instructions 658432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_658944 : Path.checkChunk context decode facts instructions 658944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_659456 : Path.checkChunk context decode facts instructions 659456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_659968 : Path.checkChunk context decode facts instructions 659968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_660480 : Path.checkChunk context decode facts instructions 660480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_660992 : Path.checkChunk context decode facts instructions 660992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_661504 : Path.checkChunk context decode facts instructions 661504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_662016 : Path.checkChunk context decode facts instructions 662016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_662528 : Path.checkChunk context decode facts instructions 662528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_663040 : Path.checkChunk context decode facts instructions 663040 512 = true := by
  decide +kernel

theorem sound_655360 (prior : ∀ n, n < 655360 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 663552 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h655872 := Path.chunk_sound context_valid decode facts instructions 655360 512
    prior checked_655360
  have h656384 := Path.chunk_sound context_valid decode facts instructions 655872 512
    h655872 checked_655872
  have h656896 := Path.chunk_sound context_valid decode facts instructions 656384 512
    h656384 checked_656384
  have h657408 := Path.chunk_sound context_valid decode facts instructions 656896 512
    h656896 checked_656896
  have h657920 := Path.chunk_sound context_valid decode facts instructions 657408 512
    h657408 checked_657408
  have h658432 := Path.chunk_sound context_valid decode facts instructions 657920 512
    h657920 checked_657920
  have h658944 := Path.chunk_sound context_valid decode facts instructions 658432 512
    h658432 checked_658432
  have h659456 := Path.chunk_sound context_valid decode facts instructions 658944 512
    h658944 checked_658944
  have h659968 := Path.chunk_sound context_valid decode facts instructions 659456 512
    h659456 checked_659456
  have h660480 := Path.chunk_sound context_valid decode facts instructions 659968 512
    h659968 checked_659968
  have h660992 := Path.chunk_sound context_valid decode facts instructions 660480 512
    h660480 checked_660480
  have h661504 := Path.chunk_sound context_valid decode facts instructions 660992 512
    h660992 checked_660992
  have h662016 := Path.chunk_sound context_valid decode facts instructions 661504 512
    h661504 checked_661504
  have h662528 := Path.chunk_sound context_valid decode facts instructions 662016 512
    h662016 checked_662016
  have h663040 := Path.chunk_sound context_valid decode facts instructions 662528 512
    h662528 checked_662528
  have h663552 := Path.chunk_sound context_valid decode facts instructions 663040 512
    h663040 checked_663040
  exact h663552

end Sporadic.Janko3.AmalgamPresentation.Cover
