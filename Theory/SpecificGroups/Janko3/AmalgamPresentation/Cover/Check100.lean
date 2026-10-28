module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_819200 : Path.checkChunk context decode facts instructions 819200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_819712 : Path.checkChunk context decode facts instructions 819712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_820224 : Path.checkChunk context decode facts instructions 820224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_820736 : Path.checkChunk context decode facts instructions 820736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_821248 : Path.checkChunk context decode facts instructions 821248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_821760 : Path.checkChunk context decode facts instructions 821760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_822272 : Path.checkChunk context decode facts instructions 822272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_822784 : Path.checkChunk context decode facts instructions 822784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_823296 : Path.checkChunk context decode facts instructions 823296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_823808 : Path.checkChunk context decode facts instructions 823808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_824320 : Path.checkChunk context decode facts instructions 824320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_824832 : Path.checkChunk context decode facts instructions 824832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_825344 : Path.checkChunk context decode facts instructions 825344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_825856 : Path.checkChunk context decode facts instructions 825856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_826368 : Path.checkChunk context decode facts instructions 826368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_826880 : Path.checkChunk context decode facts instructions 826880 512 = true := by
  decide +kernel

theorem sound_819200 (prior : ∀ n, n < 819200 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 827392 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h819712 := Path.chunk_sound context_valid decode facts instructions 819200 512
    prior checked_819200
  have h820224 := Path.chunk_sound context_valid decode facts instructions 819712 512
    h819712 checked_819712
  have h820736 := Path.chunk_sound context_valid decode facts instructions 820224 512
    h820224 checked_820224
  have h821248 := Path.chunk_sound context_valid decode facts instructions 820736 512
    h820736 checked_820736
  have h821760 := Path.chunk_sound context_valid decode facts instructions 821248 512
    h821248 checked_821248
  have h822272 := Path.chunk_sound context_valid decode facts instructions 821760 512
    h821760 checked_821760
  have h822784 := Path.chunk_sound context_valid decode facts instructions 822272 512
    h822272 checked_822272
  have h823296 := Path.chunk_sound context_valid decode facts instructions 822784 512
    h822784 checked_822784
  have h823808 := Path.chunk_sound context_valid decode facts instructions 823296 512
    h823296 checked_823296
  have h824320 := Path.chunk_sound context_valid decode facts instructions 823808 512
    h823808 checked_823808
  have h824832 := Path.chunk_sound context_valid decode facts instructions 824320 512
    h824320 checked_824320
  have h825344 := Path.chunk_sound context_valid decode facts instructions 824832 512
    h824832 checked_824832
  have h825856 := Path.chunk_sound context_valid decode facts instructions 825344 512
    h825344 checked_825344
  have h826368 := Path.chunk_sound context_valid decode facts instructions 825856 512
    h825856 checked_825856
  have h826880 := Path.chunk_sound context_valid decode facts instructions 826368 512
    h826368 checked_826368
  have h827392 := Path.chunk_sound context_valid decode facts instructions 826880 512
    h826880 checked_826880
  exact h827392

end Sporadic.Janko3.AmalgamPresentation.Cover
