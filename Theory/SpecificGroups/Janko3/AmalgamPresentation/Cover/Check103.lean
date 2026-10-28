module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_843776 : Path.checkChunk context decode facts instructions 843776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_844288 : Path.checkChunk context decode facts instructions 844288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_844800 : Path.checkChunk context decode facts instructions 844800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_845312 : Path.checkChunk context decode facts instructions 845312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_845824 : Path.checkChunk context decode facts instructions 845824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_846336 : Path.checkChunk context decode facts instructions 846336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_846848 : Path.checkChunk context decode facts instructions 846848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_847360 : Path.checkChunk context decode facts instructions 847360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_847872 : Path.checkChunk context decode facts instructions 847872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_848384 : Path.checkChunk context decode facts instructions 848384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_848896 : Path.checkChunk context decode facts instructions 848896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_849408 : Path.checkChunk context decode facts instructions 849408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_849920 : Path.checkChunk context decode facts instructions 849920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_850432 : Path.checkChunk context decode facts instructions 850432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_850944 : Path.checkChunk context decode facts instructions 850944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_851456 : Path.checkChunk context decode facts instructions 851456 512 = true := by
  decide +kernel

theorem sound_843776 (prior : ∀ n, n < 843776 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 851968 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h844288 := Path.chunk_sound context_valid decode facts instructions 843776 512
    prior checked_843776
  have h844800 := Path.chunk_sound context_valid decode facts instructions 844288 512
    h844288 checked_844288
  have h845312 := Path.chunk_sound context_valid decode facts instructions 844800 512
    h844800 checked_844800
  have h845824 := Path.chunk_sound context_valid decode facts instructions 845312 512
    h845312 checked_845312
  have h846336 := Path.chunk_sound context_valid decode facts instructions 845824 512
    h845824 checked_845824
  have h846848 := Path.chunk_sound context_valid decode facts instructions 846336 512
    h846336 checked_846336
  have h847360 := Path.chunk_sound context_valid decode facts instructions 846848 512
    h846848 checked_846848
  have h847872 := Path.chunk_sound context_valid decode facts instructions 847360 512
    h847360 checked_847360
  have h848384 := Path.chunk_sound context_valid decode facts instructions 847872 512
    h847872 checked_847872
  have h848896 := Path.chunk_sound context_valid decode facts instructions 848384 512
    h848384 checked_848384
  have h849408 := Path.chunk_sound context_valid decode facts instructions 848896 512
    h848896 checked_848896
  have h849920 := Path.chunk_sound context_valid decode facts instructions 849408 512
    h849408 checked_849408
  have h850432 := Path.chunk_sound context_valid decode facts instructions 849920 512
    h849920 checked_849920
  have h850944 := Path.chunk_sound context_valid decode facts instructions 850432 512
    h850432 checked_850432
  have h851456 := Path.chunk_sound context_valid decode facts instructions 850944 512
    h850944 checked_850944
  have h851968 := Path.chunk_sound context_valid decode facts instructions 851456 512
    h851456 checked_851456
  exact h851968

end Sporadic.Janko3.AmalgamPresentation.Cover
