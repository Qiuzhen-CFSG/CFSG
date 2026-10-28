module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_966656 : Path.checkChunk context decode facts instructions 966656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_967168 : Path.checkChunk context decode facts instructions 967168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_967680 : Path.checkChunk context decode facts instructions 967680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_968192 : Path.checkChunk context decode facts instructions 968192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_968704 : Path.checkChunk context decode facts instructions 968704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_969216 : Path.checkChunk context decode facts instructions 969216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_969728 : Path.checkChunk context decode facts instructions 969728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_970240 : Path.checkChunk context decode facts instructions 970240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_970752 : Path.checkChunk context decode facts instructions 970752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_971264 : Path.checkChunk context decode facts instructions 971264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_971776 : Path.checkChunk context decode facts instructions 971776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_972288 : Path.checkChunk context decode facts instructions 972288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_972800 : Path.checkChunk context decode facts instructions 972800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_973312 : Path.checkChunk context decode facts instructions 973312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_973824 : Path.checkChunk context decode facts instructions 973824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_974336 : Path.checkChunk context decode facts instructions 974336 512 = true := by
  decide +kernel

theorem sound_966656 (prior : ∀ n, n < 966656 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 974848 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h967168 := Path.chunk_sound context_valid decode facts instructions 966656 512
    prior checked_966656
  have h967680 := Path.chunk_sound context_valid decode facts instructions 967168 512
    h967168 checked_967168
  have h968192 := Path.chunk_sound context_valid decode facts instructions 967680 512
    h967680 checked_967680
  have h968704 := Path.chunk_sound context_valid decode facts instructions 968192 512
    h968192 checked_968192
  have h969216 := Path.chunk_sound context_valid decode facts instructions 968704 512
    h968704 checked_968704
  have h969728 := Path.chunk_sound context_valid decode facts instructions 969216 512
    h969216 checked_969216
  have h970240 := Path.chunk_sound context_valid decode facts instructions 969728 512
    h969728 checked_969728
  have h970752 := Path.chunk_sound context_valid decode facts instructions 970240 512
    h970240 checked_970240
  have h971264 := Path.chunk_sound context_valid decode facts instructions 970752 512
    h970752 checked_970752
  have h971776 := Path.chunk_sound context_valid decode facts instructions 971264 512
    h971264 checked_971264
  have h972288 := Path.chunk_sound context_valid decode facts instructions 971776 512
    h971776 checked_971776
  have h972800 := Path.chunk_sound context_valid decode facts instructions 972288 512
    h972288 checked_972288
  have h973312 := Path.chunk_sound context_valid decode facts instructions 972800 512
    h972800 checked_972800
  have h973824 := Path.chunk_sound context_valid decode facts instructions 973312 512
    h973312 checked_973312
  have h974336 := Path.chunk_sound context_valid decode facts instructions 973824 512
    h973824 checked_973824
  have h974848 := Path.chunk_sound context_valid decode facts instructions 974336 512
    h974336 checked_974336
  exact h974848

end Sporadic.Janko3.AmalgamPresentation.Cover
