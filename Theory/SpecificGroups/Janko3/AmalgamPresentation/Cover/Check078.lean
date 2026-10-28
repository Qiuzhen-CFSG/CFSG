module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_638976 : Path.checkChunk context decode facts instructions 638976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_639488 : Path.checkChunk context decode facts instructions 639488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_640000 : Path.checkChunk context decode facts instructions 640000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_640512 : Path.checkChunk context decode facts instructions 640512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_641024 : Path.checkChunk context decode facts instructions 641024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_641536 : Path.checkChunk context decode facts instructions 641536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_642048 : Path.checkChunk context decode facts instructions 642048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_642560 : Path.checkChunk context decode facts instructions 642560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_643072 : Path.checkChunk context decode facts instructions 643072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_643584 : Path.checkChunk context decode facts instructions 643584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_644096 : Path.checkChunk context decode facts instructions 644096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_644608 : Path.checkChunk context decode facts instructions 644608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_645120 : Path.checkChunk context decode facts instructions 645120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_645632 : Path.checkChunk context decode facts instructions 645632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_646144 : Path.checkChunk context decode facts instructions 646144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_646656 : Path.checkChunk context decode facts instructions 646656 512 = true := by
  decide +kernel

theorem sound_638976 (prior : ∀ n, n < 638976 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 647168 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h639488 := Path.chunk_sound context_valid decode facts instructions 638976 512
    prior checked_638976
  have h640000 := Path.chunk_sound context_valid decode facts instructions 639488 512
    h639488 checked_639488
  have h640512 := Path.chunk_sound context_valid decode facts instructions 640000 512
    h640000 checked_640000
  have h641024 := Path.chunk_sound context_valid decode facts instructions 640512 512
    h640512 checked_640512
  have h641536 := Path.chunk_sound context_valid decode facts instructions 641024 512
    h641024 checked_641024
  have h642048 := Path.chunk_sound context_valid decode facts instructions 641536 512
    h641536 checked_641536
  have h642560 := Path.chunk_sound context_valid decode facts instructions 642048 512
    h642048 checked_642048
  have h643072 := Path.chunk_sound context_valid decode facts instructions 642560 512
    h642560 checked_642560
  have h643584 := Path.chunk_sound context_valid decode facts instructions 643072 512
    h643072 checked_643072
  have h644096 := Path.chunk_sound context_valid decode facts instructions 643584 512
    h643584 checked_643584
  have h644608 := Path.chunk_sound context_valid decode facts instructions 644096 512
    h644096 checked_644096
  have h645120 := Path.chunk_sound context_valid decode facts instructions 644608 512
    h644608 checked_644608
  have h645632 := Path.chunk_sound context_valid decode facts instructions 645120 512
    h645120 checked_645120
  have h646144 := Path.chunk_sound context_valid decode facts instructions 645632 512
    h645632 checked_645632
  have h646656 := Path.chunk_sound context_valid decode facts instructions 646144 512
    h646144 checked_646144
  have h647168 := Path.chunk_sound context_valid decode facts instructions 646656 512
    h646656 checked_646656
  exact h647168

end Sporadic.Janko3.AmalgamPresentation.Cover
