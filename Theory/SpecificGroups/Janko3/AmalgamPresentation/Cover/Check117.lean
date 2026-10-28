module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_958464 : Path.checkChunk context decode facts instructions 958464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_958976 : Path.checkChunk context decode facts instructions 958976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_959488 : Path.checkChunk context decode facts instructions 959488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_960000 : Path.checkChunk context decode facts instructions 960000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_960512 : Path.checkChunk context decode facts instructions 960512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_961024 : Path.checkChunk context decode facts instructions 961024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_961536 : Path.checkChunk context decode facts instructions 961536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_962048 : Path.checkChunk context decode facts instructions 962048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_962560 : Path.checkChunk context decode facts instructions 962560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_963072 : Path.checkChunk context decode facts instructions 963072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_963584 : Path.checkChunk context decode facts instructions 963584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_964096 : Path.checkChunk context decode facts instructions 964096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_964608 : Path.checkChunk context decode facts instructions 964608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_965120 : Path.checkChunk context decode facts instructions 965120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_965632 : Path.checkChunk context decode facts instructions 965632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_966144 : Path.checkChunk context decode facts instructions 966144 512 = true := by
  decide +kernel

theorem sound_958464 (prior : ∀ n, n < 958464 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 966656 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h958976 := Path.chunk_sound context_valid decode facts instructions 958464 512
    prior checked_958464
  have h959488 := Path.chunk_sound context_valid decode facts instructions 958976 512
    h958976 checked_958976
  have h960000 := Path.chunk_sound context_valid decode facts instructions 959488 512
    h959488 checked_959488
  have h960512 := Path.chunk_sound context_valid decode facts instructions 960000 512
    h960000 checked_960000
  have h961024 := Path.chunk_sound context_valid decode facts instructions 960512 512
    h960512 checked_960512
  have h961536 := Path.chunk_sound context_valid decode facts instructions 961024 512
    h961024 checked_961024
  have h962048 := Path.chunk_sound context_valid decode facts instructions 961536 512
    h961536 checked_961536
  have h962560 := Path.chunk_sound context_valid decode facts instructions 962048 512
    h962048 checked_962048
  have h963072 := Path.chunk_sound context_valid decode facts instructions 962560 512
    h962560 checked_962560
  have h963584 := Path.chunk_sound context_valid decode facts instructions 963072 512
    h963072 checked_963072
  have h964096 := Path.chunk_sound context_valid decode facts instructions 963584 512
    h963584 checked_963584
  have h964608 := Path.chunk_sound context_valid decode facts instructions 964096 512
    h964096 checked_964096
  have h965120 := Path.chunk_sound context_valid decode facts instructions 964608 512
    h964608 checked_964608
  have h965632 := Path.chunk_sound context_valid decode facts instructions 965120 512
    h965120 checked_965120
  have h966144 := Path.chunk_sound context_valid decode facts instructions 965632 512
    h965632 checked_965632
  have h966656 := Path.chunk_sound context_valid decode facts instructions 966144 512
    h966144 checked_966144
  exact h966656

end Sporadic.Janko3.AmalgamPresentation.Cover
