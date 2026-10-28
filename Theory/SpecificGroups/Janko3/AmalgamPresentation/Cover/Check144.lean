module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1179648 : Path.checkChunk context decode facts instructions 1179648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1180160 : Path.checkChunk context decode facts instructions 1180160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1180672 : Path.checkChunk context decode facts instructions 1180672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1181184 : Path.checkChunk context decode facts instructions 1181184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1181696 : Path.checkChunk context decode facts instructions 1181696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1182208 : Path.checkChunk context decode facts instructions 1182208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1182720 : Path.checkChunk context decode facts instructions 1182720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1183232 : Path.checkChunk context decode facts instructions 1183232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1183744 : Path.checkChunk context decode facts instructions 1183744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1184256 : Path.checkChunk context decode facts instructions 1184256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1184768 : Path.checkChunk context decode facts instructions 1184768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1185280 : Path.checkChunk context decode facts instructions 1185280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1185792 : Path.checkChunk context decode facts instructions 1185792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1186304 : Path.checkChunk context decode facts instructions 1186304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1186816 : Path.checkChunk context decode facts instructions 1186816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1187328 : Path.checkChunk context decode facts instructions 1187328 512 = true := by
  decide +kernel

theorem sound_1179648 (prior : ∀ n, n < 1179648 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1187840 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1180160 := Path.chunk_sound context_valid decode facts instructions 1179648 512
    prior checked_1179648
  have h1180672 := Path.chunk_sound context_valid decode facts instructions 1180160 512
    h1180160 checked_1180160
  have h1181184 := Path.chunk_sound context_valid decode facts instructions 1180672 512
    h1180672 checked_1180672
  have h1181696 := Path.chunk_sound context_valid decode facts instructions 1181184 512
    h1181184 checked_1181184
  have h1182208 := Path.chunk_sound context_valid decode facts instructions 1181696 512
    h1181696 checked_1181696
  have h1182720 := Path.chunk_sound context_valid decode facts instructions 1182208 512
    h1182208 checked_1182208
  have h1183232 := Path.chunk_sound context_valid decode facts instructions 1182720 512
    h1182720 checked_1182720
  have h1183744 := Path.chunk_sound context_valid decode facts instructions 1183232 512
    h1183232 checked_1183232
  have h1184256 := Path.chunk_sound context_valid decode facts instructions 1183744 512
    h1183744 checked_1183744
  have h1184768 := Path.chunk_sound context_valid decode facts instructions 1184256 512
    h1184256 checked_1184256
  have h1185280 := Path.chunk_sound context_valid decode facts instructions 1184768 512
    h1184768 checked_1184768
  have h1185792 := Path.chunk_sound context_valid decode facts instructions 1185280 512
    h1185280 checked_1185280
  have h1186304 := Path.chunk_sound context_valid decode facts instructions 1185792 512
    h1185792 checked_1185792
  have h1186816 := Path.chunk_sound context_valid decode facts instructions 1186304 512
    h1186304 checked_1186304
  have h1187328 := Path.chunk_sound context_valid decode facts instructions 1186816 512
    h1186816 checked_1186816
  have h1187840 := Path.chunk_sound context_valid decode facts instructions 1187328 512
    h1187328 checked_1187328
  exact h1187840

end Sporadic.Janko3.AmalgamPresentation.Cover
