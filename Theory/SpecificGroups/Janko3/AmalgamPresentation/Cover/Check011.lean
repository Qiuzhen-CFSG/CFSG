module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_90112 : Path.checkChunk context decode facts instructions 90112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_90624 : Path.checkChunk context decode facts instructions 90624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_91136 : Path.checkChunk context decode facts instructions 91136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_91648 : Path.checkChunk context decode facts instructions 91648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_92160 : Path.checkChunk context decode facts instructions 92160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_92672 : Path.checkChunk context decode facts instructions 92672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_93184 : Path.checkChunk context decode facts instructions 93184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_93696 : Path.checkChunk context decode facts instructions 93696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_94208 : Path.checkChunk context decode facts instructions 94208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_94720 : Path.checkChunk context decode facts instructions 94720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_95232 : Path.checkChunk context decode facts instructions 95232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_95744 : Path.checkChunk context decode facts instructions 95744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_96256 : Path.checkChunk context decode facts instructions 96256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_96768 : Path.checkChunk context decode facts instructions 96768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_97280 : Path.checkChunk context decode facts instructions 97280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_97792 : Path.checkChunk context decode facts instructions 97792 512 = true := by
  decide +kernel

theorem sound_90112 (prior : ∀ n, n < 90112 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 98304 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h90624 := Path.chunk_sound context_valid decode facts instructions 90112 512
    prior checked_90112
  have h91136 := Path.chunk_sound context_valid decode facts instructions 90624 512
    h90624 checked_90624
  have h91648 := Path.chunk_sound context_valid decode facts instructions 91136 512
    h91136 checked_91136
  have h92160 := Path.chunk_sound context_valid decode facts instructions 91648 512
    h91648 checked_91648
  have h92672 := Path.chunk_sound context_valid decode facts instructions 92160 512
    h92160 checked_92160
  have h93184 := Path.chunk_sound context_valid decode facts instructions 92672 512
    h92672 checked_92672
  have h93696 := Path.chunk_sound context_valid decode facts instructions 93184 512
    h93184 checked_93184
  have h94208 := Path.chunk_sound context_valid decode facts instructions 93696 512
    h93696 checked_93696
  have h94720 := Path.chunk_sound context_valid decode facts instructions 94208 512
    h94208 checked_94208
  have h95232 := Path.chunk_sound context_valid decode facts instructions 94720 512
    h94720 checked_94720
  have h95744 := Path.chunk_sound context_valid decode facts instructions 95232 512
    h95232 checked_95232
  have h96256 := Path.chunk_sound context_valid decode facts instructions 95744 512
    h95744 checked_95744
  have h96768 := Path.chunk_sound context_valid decode facts instructions 96256 512
    h96256 checked_96256
  have h97280 := Path.chunk_sound context_valid decode facts instructions 96768 512
    h96768 checked_96768
  have h97792 := Path.chunk_sound context_valid decode facts instructions 97280 512
    h97280 checked_97280
  have h98304 := Path.chunk_sound context_valid decode facts instructions 97792 512
    h97792 checked_97792
  exact h98304

end Sporadic.Janko3.AmalgamPresentation.Cover
