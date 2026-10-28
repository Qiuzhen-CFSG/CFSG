module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_679936 : Path.checkChunk context decode facts instructions 679936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_680448 : Path.checkChunk context decode facts instructions 680448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_680960 : Path.checkChunk context decode facts instructions 680960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_681472 : Path.checkChunk context decode facts instructions 681472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_681984 : Path.checkChunk context decode facts instructions 681984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_682496 : Path.checkChunk context decode facts instructions 682496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_683008 : Path.checkChunk context decode facts instructions 683008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_683520 : Path.checkChunk context decode facts instructions 683520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_684032 : Path.checkChunk context decode facts instructions 684032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_684544 : Path.checkChunk context decode facts instructions 684544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_685056 : Path.checkChunk context decode facts instructions 685056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_685568 : Path.checkChunk context decode facts instructions 685568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_686080 : Path.checkChunk context decode facts instructions 686080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_686592 : Path.checkChunk context decode facts instructions 686592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_687104 : Path.checkChunk context decode facts instructions 687104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_687616 : Path.checkChunk context decode facts instructions 687616 512 = true := by
  decide +kernel

theorem sound_679936 (prior : ∀ n, n < 679936 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 688128 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h680448 := Path.chunk_sound context_valid decode facts instructions 679936 512
    prior checked_679936
  have h680960 := Path.chunk_sound context_valid decode facts instructions 680448 512
    h680448 checked_680448
  have h681472 := Path.chunk_sound context_valid decode facts instructions 680960 512
    h680960 checked_680960
  have h681984 := Path.chunk_sound context_valid decode facts instructions 681472 512
    h681472 checked_681472
  have h682496 := Path.chunk_sound context_valid decode facts instructions 681984 512
    h681984 checked_681984
  have h683008 := Path.chunk_sound context_valid decode facts instructions 682496 512
    h682496 checked_682496
  have h683520 := Path.chunk_sound context_valid decode facts instructions 683008 512
    h683008 checked_683008
  have h684032 := Path.chunk_sound context_valid decode facts instructions 683520 512
    h683520 checked_683520
  have h684544 := Path.chunk_sound context_valid decode facts instructions 684032 512
    h684032 checked_684032
  have h685056 := Path.chunk_sound context_valid decode facts instructions 684544 512
    h684544 checked_684544
  have h685568 := Path.chunk_sound context_valid decode facts instructions 685056 512
    h685056 checked_685056
  have h686080 := Path.chunk_sound context_valid decode facts instructions 685568 512
    h685568 checked_685568
  have h686592 := Path.chunk_sound context_valid decode facts instructions 686080 512
    h686080 checked_686080
  have h687104 := Path.chunk_sound context_valid decode facts instructions 686592 512
    h686592 checked_686592
  have h687616 := Path.chunk_sound context_valid decode facts instructions 687104 512
    h687104 checked_687104
  have h688128 := Path.chunk_sound context_valid decode facts instructions 687616 512
    h687616 checked_687616
  exact h688128

end Sporadic.Janko3.AmalgamPresentation.Cover
