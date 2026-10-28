module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_925696 : Path.checkChunk context decode facts instructions 925696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_926208 : Path.checkChunk context decode facts instructions 926208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_926720 : Path.checkChunk context decode facts instructions 926720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_927232 : Path.checkChunk context decode facts instructions 927232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_927744 : Path.checkChunk context decode facts instructions 927744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_928256 : Path.checkChunk context decode facts instructions 928256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_928768 : Path.checkChunk context decode facts instructions 928768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_929280 : Path.checkChunk context decode facts instructions 929280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_929792 : Path.checkChunk context decode facts instructions 929792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_930304 : Path.checkChunk context decode facts instructions 930304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_930816 : Path.checkChunk context decode facts instructions 930816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_931328 : Path.checkChunk context decode facts instructions 931328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_931840 : Path.checkChunk context decode facts instructions 931840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_932352 : Path.checkChunk context decode facts instructions 932352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_932864 : Path.checkChunk context decode facts instructions 932864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_933376 : Path.checkChunk context decode facts instructions 933376 512 = true := by
  decide +kernel

theorem sound_925696 (prior : ∀ n, n < 925696 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 933888 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h926208 := Path.chunk_sound context_valid decode facts instructions 925696 512
    prior checked_925696
  have h926720 := Path.chunk_sound context_valid decode facts instructions 926208 512
    h926208 checked_926208
  have h927232 := Path.chunk_sound context_valid decode facts instructions 926720 512
    h926720 checked_926720
  have h927744 := Path.chunk_sound context_valid decode facts instructions 927232 512
    h927232 checked_927232
  have h928256 := Path.chunk_sound context_valid decode facts instructions 927744 512
    h927744 checked_927744
  have h928768 := Path.chunk_sound context_valid decode facts instructions 928256 512
    h928256 checked_928256
  have h929280 := Path.chunk_sound context_valid decode facts instructions 928768 512
    h928768 checked_928768
  have h929792 := Path.chunk_sound context_valid decode facts instructions 929280 512
    h929280 checked_929280
  have h930304 := Path.chunk_sound context_valid decode facts instructions 929792 512
    h929792 checked_929792
  have h930816 := Path.chunk_sound context_valid decode facts instructions 930304 512
    h930304 checked_930304
  have h931328 := Path.chunk_sound context_valid decode facts instructions 930816 512
    h930816 checked_930816
  have h931840 := Path.chunk_sound context_valid decode facts instructions 931328 512
    h931328 checked_931328
  have h932352 := Path.chunk_sound context_valid decode facts instructions 931840 512
    h931840 checked_931840
  have h932864 := Path.chunk_sound context_valid decode facts instructions 932352 512
    h932352 checked_932352
  have h933376 := Path.chunk_sound context_valid decode facts instructions 932864 512
    h932864 checked_932864
  have h933888 := Path.chunk_sound context_valid decode facts instructions 933376 512
    h933376 checked_933376
  exact h933888

end Sporadic.Janko3.AmalgamPresentation.Cover
