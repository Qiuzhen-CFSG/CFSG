module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_827392 : Path.checkChunk context decode facts instructions 827392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_827904 : Path.checkChunk context decode facts instructions 827904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_828416 : Path.checkChunk context decode facts instructions 828416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_828928 : Path.checkChunk context decode facts instructions 828928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_829440 : Path.checkChunk context decode facts instructions 829440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_829952 : Path.checkChunk context decode facts instructions 829952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_830464 : Path.checkChunk context decode facts instructions 830464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_830976 : Path.checkChunk context decode facts instructions 830976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_831488 : Path.checkChunk context decode facts instructions 831488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_832000 : Path.checkChunk context decode facts instructions 832000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_832512 : Path.checkChunk context decode facts instructions 832512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_833024 : Path.checkChunk context decode facts instructions 833024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_833536 : Path.checkChunk context decode facts instructions 833536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_834048 : Path.checkChunk context decode facts instructions 834048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_834560 : Path.checkChunk context decode facts instructions 834560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_835072 : Path.checkChunk context decode facts instructions 835072 512 = true := by
  decide +kernel

theorem sound_827392 (prior : ∀ n, n < 827392 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 835584 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h827904 := Path.chunk_sound context_valid decode facts instructions 827392 512
    prior checked_827392
  have h828416 := Path.chunk_sound context_valid decode facts instructions 827904 512
    h827904 checked_827904
  have h828928 := Path.chunk_sound context_valid decode facts instructions 828416 512
    h828416 checked_828416
  have h829440 := Path.chunk_sound context_valid decode facts instructions 828928 512
    h828928 checked_828928
  have h829952 := Path.chunk_sound context_valid decode facts instructions 829440 512
    h829440 checked_829440
  have h830464 := Path.chunk_sound context_valid decode facts instructions 829952 512
    h829952 checked_829952
  have h830976 := Path.chunk_sound context_valid decode facts instructions 830464 512
    h830464 checked_830464
  have h831488 := Path.chunk_sound context_valid decode facts instructions 830976 512
    h830976 checked_830976
  have h832000 := Path.chunk_sound context_valid decode facts instructions 831488 512
    h831488 checked_831488
  have h832512 := Path.chunk_sound context_valid decode facts instructions 832000 512
    h832000 checked_832000
  have h833024 := Path.chunk_sound context_valid decode facts instructions 832512 512
    h832512 checked_832512
  have h833536 := Path.chunk_sound context_valid decode facts instructions 833024 512
    h833024 checked_833024
  have h834048 := Path.chunk_sound context_valid decode facts instructions 833536 512
    h833536 checked_833536
  have h834560 := Path.chunk_sound context_valid decode facts instructions 834048 512
    h834048 checked_834048
  have h835072 := Path.chunk_sound context_valid decode facts instructions 834560 512
    h834560 checked_834560
  have h835584 := Path.chunk_sound context_valid decode facts instructions 835072 512
    h835072 checked_835072
  exact h835584

end Sporadic.Janko3.AmalgamPresentation.Cover
