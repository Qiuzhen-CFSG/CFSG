module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_524288 : Path.checkChunk context decode facts instructions 524288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_524800 : Path.checkChunk context decode facts instructions 524800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_525312 : Path.checkChunk context decode facts instructions 525312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_525824 : Path.checkChunk context decode facts instructions 525824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_526336 : Path.checkChunk context decode facts instructions 526336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_526848 : Path.checkChunk context decode facts instructions 526848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_527360 : Path.checkChunk context decode facts instructions 527360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_527872 : Path.checkChunk context decode facts instructions 527872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_528384 : Path.checkChunk context decode facts instructions 528384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_528896 : Path.checkChunk context decode facts instructions 528896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_529408 : Path.checkChunk context decode facts instructions 529408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_529920 : Path.checkChunk context decode facts instructions 529920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_530432 : Path.checkChunk context decode facts instructions 530432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_530944 : Path.checkChunk context decode facts instructions 530944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_531456 : Path.checkChunk context decode facts instructions 531456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_531968 : Path.checkChunk context decode facts instructions 531968 512 = true := by
  decide +kernel

theorem sound_524288 (prior : ∀ n, n < 524288 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 532480 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h524800 := Path.chunk_sound context_valid decode facts instructions 524288 512
    prior checked_524288
  have h525312 := Path.chunk_sound context_valid decode facts instructions 524800 512
    h524800 checked_524800
  have h525824 := Path.chunk_sound context_valid decode facts instructions 525312 512
    h525312 checked_525312
  have h526336 := Path.chunk_sound context_valid decode facts instructions 525824 512
    h525824 checked_525824
  have h526848 := Path.chunk_sound context_valid decode facts instructions 526336 512
    h526336 checked_526336
  have h527360 := Path.chunk_sound context_valid decode facts instructions 526848 512
    h526848 checked_526848
  have h527872 := Path.chunk_sound context_valid decode facts instructions 527360 512
    h527360 checked_527360
  have h528384 := Path.chunk_sound context_valid decode facts instructions 527872 512
    h527872 checked_527872
  have h528896 := Path.chunk_sound context_valid decode facts instructions 528384 512
    h528384 checked_528384
  have h529408 := Path.chunk_sound context_valid decode facts instructions 528896 512
    h528896 checked_528896
  have h529920 := Path.chunk_sound context_valid decode facts instructions 529408 512
    h529408 checked_529408
  have h530432 := Path.chunk_sound context_valid decode facts instructions 529920 512
    h529920 checked_529920
  have h530944 := Path.chunk_sound context_valid decode facts instructions 530432 512
    h530432 checked_530432
  have h531456 := Path.chunk_sound context_valid decode facts instructions 530944 512
    h530944 checked_530944
  have h531968 := Path.chunk_sound context_valid decode facts instructions 531456 512
    h531456 checked_531456
  have h532480 := Path.chunk_sound context_valid decode facts instructions 531968 512
    h531968 checked_531968
  exact h532480

end Sporadic.Janko3.AmalgamPresentation.Cover
