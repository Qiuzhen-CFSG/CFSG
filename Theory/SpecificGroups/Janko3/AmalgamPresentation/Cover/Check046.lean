module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_376832 : Path.checkChunk context decode facts instructions 376832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_377344 : Path.checkChunk context decode facts instructions 377344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_377856 : Path.checkChunk context decode facts instructions 377856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_378368 : Path.checkChunk context decode facts instructions 378368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_378880 : Path.checkChunk context decode facts instructions 378880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_379392 : Path.checkChunk context decode facts instructions 379392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_379904 : Path.checkChunk context decode facts instructions 379904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_380416 : Path.checkChunk context decode facts instructions 380416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_380928 : Path.checkChunk context decode facts instructions 380928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_381440 : Path.checkChunk context decode facts instructions 381440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_381952 : Path.checkChunk context decode facts instructions 381952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_382464 : Path.checkChunk context decode facts instructions 382464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_382976 : Path.checkChunk context decode facts instructions 382976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_383488 : Path.checkChunk context decode facts instructions 383488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_384000 : Path.checkChunk context decode facts instructions 384000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_384512 : Path.checkChunk context decode facts instructions 384512 512 = true := by
  decide +kernel

theorem sound_376832 (prior : ∀ n, n < 376832 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 385024 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h377344 := Path.chunk_sound context_valid decode facts instructions 376832 512
    prior checked_376832
  have h377856 := Path.chunk_sound context_valid decode facts instructions 377344 512
    h377344 checked_377344
  have h378368 := Path.chunk_sound context_valid decode facts instructions 377856 512
    h377856 checked_377856
  have h378880 := Path.chunk_sound context_valid decode facts instructions 378368 512
    h378368 checked_378368
  have h379392 := Path.chunk_sound context_valid decode facts instructions 378880 512
    h378880 checked_378880
  have h379904 := Path.chunk_sound context_valid decode facts instructions 379392 512
    h379392 checked_379392
  have h380416 := Path.chunk_sound context_valid decode facts instructions 379904 512
    h379904 checked_379904
  have h380928 := Path.chunk_sound context_valid decode facts instructions 380416 512
    h380416 checked_380416
  have h381440 := Path.chunk_sound context_valid decode facts instructions 380928 512
    h380928 checked_380928
  have h381952 := Path.chunk_sound context_valid decode facts instructions 381440 512
    h381440 checked_381440
  have h382464 := Path.chunk_sound context_valid decode facts instructions 381952 512
    h381952 checked_381952
  have h382976 := Path.chunk_sound context_valid decode facts instructions 382464 512
    h382464 checked_382464
  have h383488 := Path.chunk_sound context_valid decode facts instructions 382976 512
    h382976 checked_382976
  have h384000 := Path.chunk_sound context_valid decode facts instructions 383488 512
    h383488 checked_383488
  have h384512 := Path.chunk_sound context_valid decode facts instructions 384000 512
    h384000 checked_384000
  have h385024 := Path.chunk_sound context_valid decode facts instructions 384512 512
    h384512 checked_384512
  exact h385024

end Sporadic.Janko3.AmalgamPresentation.Cover
