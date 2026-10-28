module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_262144 : Path.checkChunk context decode facts instructions 262144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_262656 : Path.checkChunk context decode facts instructions 262656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_263168 : Path.checkChunk context decode facts instructions 263168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_263680 : Path.checkChunk context decode facts instructions 263680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_264192 : Path.checkChunk context decode facts instructions 264192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_264704 : Path.checkChunk context decode facts instructions 264704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_265216 : Path.checkChunk context decode facts instructions 265216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_265728 : Path.checkChunk context decode facts instructions 265728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_266240 : Path.checkChunk context decode facts instructions 266240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_266752 : Path.checkChunk context decode facts instructions 266752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_267264 : Path.checkChunk context decode facts instructions 267264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_267776 : Path.checkChunk context decode facts instructions 267776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_268288 : Path.checkChunk context decode facts instructions 268288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_268800 : Path.checkChunk context decode facts instructions 268800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_269312 : Path.checkChunk context decode facts instructions 269312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_269824 : Path.checkChunk context decode facts instructions 269824 512 = true := by
  decide +kernel

theorem sound_262144 (prior : ∀ n, n < 262144 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 270336 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h262656 := Path.chunk_sound context_valid decode facts instructions 262144 512
    prior checked_262144
  have h263168 := Path.chunk_sound context_valid decode facts instructions 262656 512
    h262656 checked_262656
  have h263680 := Path.chunk_sound context_valid decode facts instructions 263168 512
    h263168 checked_263168
  have h264192 := Path.chunk_sound context_valid decode facts instructions 263680 512
    h263680 checked_263680
  have h264704 := Path.chunk_sound context_valid decode facts instructions 264192 512
    h264192 checked_264192
  have h265216 := Path.chunk_sound context_valid decode facts instructions 264704 512
    h264704 checked_264704
  have h265728 := Path.chunk_sound context_valid decode facts instructions 265216 512
    h265216 checked_265216
  have h266240 := Path.chunk_sound context_valid decode facts instructions 265728 512
    h265728 checked_265728
  have h266752 := Path.chunk_sound context_valid decode facts instructions 266240 512
    h266240 checked_266240
  have h267264 := Path.chunk_sound context_valid decode facts instructions 266752 512
    h266752 checked_266752
  have h267776 := Path.chunk_sound context_valid decode facts instructions 267264 512
    h267264 checked_267264
  have h268288 := Path.chunk_sound context_valid decode facts instructions 267776 512
    h267776 checked_267776
  have h268800 := Path.chunk_sound context_valid decode facts instructions 268288 512
    h268288 checked_268288
  have h269312 := Path.chunk_sound context_valid decode facts instructions 268800 512
    h268800 checked_268800
  have h269824 := Path.chunk_sound context_valid decode facts instructions 269312 512
    h269312 checked_269312
  have h270336 := Path.chunk_sound context_valid decode facts instructions 269824 512
    h269824 checked_269824
  exact h270336

end Sporadic.Janko3.AmalgamPresentation.Cover
