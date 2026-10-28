module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_385024 : Path.checkChunk context decode facts instructions 385024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_385536 : Path.checkChunk context decode facts instructions 385536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_386048 : Path.checkChunk context decode facts instructions 386048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_386560 : Path.checkChunk context decode facts instructions 386560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_387072 : Path.checkChunk context decode facts instructions 387072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_387584 : Path.checkChunk context decode facts instructions 387584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_388096 : Path.checkChunk context decode facts instructions 388096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_388608 : Path.checkChunk context decode facts instructions 388608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_389120 : Path.checkChunk context decode facts instructions 389120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_389632 : Path.checkChunk context decode facts instructions 389632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_390144 : Path.checkChunk context decode facts instructions 390144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_390656 : Path.checkChunk context decode facts instructions 390656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_391168 : Path.checkChunk context decode facts instructions 391168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_391680 : Path.checkChunk context decode facts instructions 391680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_392192 : Path.checkChunk context decode facts instructions 392192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_392704 : Path.checkChunk context decode facts instructions 392704 512 = true := by
  decide +kernel

theorem sound_385024 (prior : ∀ n, n < 385024 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 393216 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h385536 := Path.chunk_sound context_valid decode facts instructions 385024 512
    prior checked_385024
  have h386048 := Path.chunk_sound context_valid decode facts instructions 385536 512
    h385536 checked_385536
  have h386560 := Path.chunk_sound context_valid decode facts instructions 386048 512
    h386048 checked_386048
  have h387072 := Path.chunk_sound context_valid decode facts instructions 386560 512
    h386560 checked_386560
  have h387584 := Path.chunk_sound context_valid decode facts instructions 387072 512
    h387072 checked_387072
  have h388096 := Path.chunk_sound context_valid decode facts instructions 387584 512
    h387584 checked_387584
  have h388608 := Path.chunk_sound context_valid decode facts instructions 388096 512
    h388096 checked_388096
  have h389120 := Path.chunk_sound context_valid decode facts instructions 388608 512
    h388608 checked_388608
  have h389632 := Path.chunk_sound context_valid decode facts instructions 389120 512
    h389120 checked_389120
  have h390144 := Path.chunk_sound context_valid decode facts instructions 389632 512
    h389632 checked_389632
  have h390656 := Path.chunk_sound context_valid decode facts instructions 390144 512
    h390144 checked_390144
  have h391168 := Path.chunk_sound context_valid decode facts instructions 390656 512
    h390656 checked_390656
  have h391680 := Path.chunk_sound context_valid decode facts instructions 391168 512
    h391168 checked_391168
  have h392192 := Path.chunk_sound context_valid decode facts instructions 391680 512
    h391680 checked_391680
  have h392704 := Path.chunk_sound context_valid decode facts instructions 392192 512
    h392192 checked_392192
  have h393216 := Path.chunk_sound context_valid decode facts instructions 392704 512
    h392704 checked_392704
  exact h393216

end Sporadic.Janko3.AmalgamPresentation.Cover
