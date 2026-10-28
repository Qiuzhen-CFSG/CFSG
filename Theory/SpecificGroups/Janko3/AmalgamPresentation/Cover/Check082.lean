module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_671744 : Path.checkChunk context decode facts instructions 671744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_672256 : Path.checkChunk context decode facts instructions 672256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_672768 : Path.checkChunk context decode facts instructions 672768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_673280 : Path.checkChunk context decode facts instructions 673280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_673792 : Path.checkChunk context decode facts instructions 673792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_674304 : Path.checkChunk context decode facts instructions 674304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_674816 : Path.checkChunk context decode facts instructions 674816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_675328 : Path.checkChunk context decode facts instructions 675328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_675840 : Path.checkChunk context decode facts instructions 675840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_676352 : Path.checkChunk context decode facts instructions 676352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_676864 : Path.checkChunk context decode facts instructions 676864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_677376 : Path.checkChunk context decode facts instructions 677376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_677888 : Path.checkChunk context decode facts instructions 677888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_678400 : Path.checkChunk context decode facts instructions 678400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_678912 : Path.checkChunk context decode facts instructions 678912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_679424 : Path.checkChunk context decode facts instructions 679424 512 = true := by
  decide +kernel

theorem sound_671744 (prior : ∀ n, n < 671744 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 679936 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h672256 := Path.chunk_sound context_valid decode facts instructions 671744 512
    prior checked_671744
  have h672768 := Path.chunk_sound context_valid decode facts instructions 672256 512
    h672256 checked_672256
  have h673280 := Path.chunk_sound context_valid decode facts instructions 672768 512
    h672768 checked_672768
  have h673792 := Path.chunk_sound context_valid decode facts instructions 673280 512
    h673280 checked_673280
  have h674304 := Path.chunk_sound context_valid decode facts instructions 673792 512
    h673792 checked_673792
  have h674816 := Path.chunk_sound context_valid decode facts instructions 674304 512
    h674304 checked_674304
  have h675328 := Path.chunk_sound context_valid decode facts instructions 674816 512
    h674816 checked_674816
  have h675840 := Path.chunk_sound context_valid decode facts instructions 675328 512
    h675328 checked_675328
  have h676352 := Path.chunk_sound context_valid decode facts instructions 675840 512
    h675840 checked_675840
  have h676864 := Path.chunk_sound context_valid decode facts instructions 676352 512
    h676352 checked_676352
  have h677376 := Path.chunk_sound context_valid decode facts instructions 676864 512
    h676864 checked_676864
  have h677888 := Path.chunk_sound context_valid decode facts instructions 677376 512
    h677376 checked_677376
  have h678400 := Path.chunk_sound context_valid decode facts instructions 677888 512
    h677888 checked_677888
  have h678912 := Path.chunk_sound context_valid decode facts instructions 678400 512
    h678400 checked_678400
  have h679424 := Path.chunk_sound context_valid decode facts instructions 678912 512
    h678912 checked_678912
  have h679936 := Path.chunk_sound context_valid decode facts instructions 679424 512
    h679424 checked_679424
  exact h679936

end Sporadic.Janko3.AmalgamPresentation.Cover
