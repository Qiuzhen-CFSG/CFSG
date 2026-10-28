module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_737280 : Path.checkChunk context decode facts instructions 737280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_737792 : Path.checkChunk context decode facts instructions 737792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_738304 : Path.checkChunk context decode facts instructions 738304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_738816 : Path.checkChunk context decode facts instructions 738816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_739328 : Path.checkChunk context decode facts instructions 739328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_739840 : Path.checkChunk context decode facts instructions 739840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_740352 : Path.checkChunk context decode facts instructions 740352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_740864 : Path.checkChunk context decode facts instructions 740864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_741376 : Path.checkChunk context decode facts instructions 741376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_741888 : Path.checkChunk context decode facts instructions 741888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_742400 : Path.checkChunk context decode facts instructions 742400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_742912 : Path.checkChunk context decode facts instructions 742912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_743424 : Path.checkChunk context decode facts instructions 743424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_743936 : Path.checkChunk context decode facts instructions 743936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_744448 : Path.checkChunk context decode facts instructions 744448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_744960 : Path.checkChunk context decode facts instructions 744960 512 = true := by
  decide +kernel

theorem sound_737280 (prior : ∀ n, n < 737280 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 745472 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h737792 := Path.chunk_sound context_valid decode facts instructions 737280 512
    prior checked_737280
  have h738304 := Path.chunk_sound context_valid decode facts instructions 737792 512
    h737792 checked_737792
  have h738816 := Path.chunk_sound context_valid decode facts instructions 738304 512
    h738304 checked_738304
  have h739328 := Path.chunk_sound context_valid decode facts instructions 738816 512
    h738816 checked_738816
  have h739840 := Path.chunk_sound context_valid decode facts instructions 739328 512
    h739328 checked_739328
  have h740352 := Path.chunk_sound context_valid decode facts instructions 739840 512
    h739840 checked_739840
  have h740864 := Path.chunk_sound context_valid decode facts instructions 740352 512
    h740352 checked_740352
  have h741376 := Path.chunk_sound context_valid decode facts instructions 740864 512
    h740864 checked_740864
  have h741888 := Path.chunk_sound context_valid decode facts instructions 741376 512
    h741376 checked_741376
  have h742400 := Path.chunk_sound context_valid decode facts instructions 741888 512
    h741888 checked_741888
  have h742912 := Path.chunk_sound context_valid decode facts instructions 742400 512
    h742400 checked_742400
  have h743424 := Path.chunk_sound context_valid decode facts instructions 742912 512
    h742912 checked_742912
  have h743936 := Path.chunk_sound context_valid decode facts instructions 743424 512
    h743424 checked_743424
  have h744448 := Path.chunk_sound context_valid decode facts instructions 743936 512
    h743936 checked_743936
  have h744960 := Path.chunk_sound context_valid decode facts instructions 744448 512
    h744448 checked_744448
  have h745472 := Path.chunk_sound context_valid decode facts instructions 744960 512
    h744960 checked_744960
  exact h745472

end Sporadic.Janko3.AmalgamPresentation.Cover
