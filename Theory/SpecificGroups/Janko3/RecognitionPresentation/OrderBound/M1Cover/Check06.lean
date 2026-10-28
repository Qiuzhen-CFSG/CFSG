module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Tables

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_98304 : Scan.checkChunk context facts instructions 98304 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_99328 : Scan.checkChunk context facts instructions 99328 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_100352 : Scan.checkChunk context facts instructions 100352 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_101376 : Scan.checkChunk context facts instructions 101376 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_102400 : Scan.checkChunk context facts instructions 102400 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_103424 : Scan.checkChunk context facts instructions 103424 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_104448 : Scan.checkChunk context facts instructions 104448 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_105472 : Scan.checkChunk context facts instructions 105472 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_106496 : Scan.checkChunk context facts instructions 106496 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_107520 : Scan.checkChunk context facts instructions 107520 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_108544 : Scan.checkChunk context facts instructions 108544 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_109568 : Scan.checkChunk context facts instructions 109568 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_110592 : Scan.checkChunk context facts instructions 110592 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_111616 : Scan.checkChunk context facts instructions 111616 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_112640 : Scan.checkChunk context facts instructions 112640 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_113664 : Scan.checkChunk context facts instructions 113664 1024 = true := by
  decide +kernel

theorem sound_98304 (prior : ∀ n, n < 98304 →
    Holds M1 generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 114688 → Holds M1 generator (definitions.repr generator) (facts n) := by
  have h99328 := Scan.chunk_sound context_valid facts instructions 98304 1024
    prior checked_98304
  have h100352 := Scan.chunk_sound context_valid facts instructions 99328 1024
    h99328 checked_99328
  have h101376 := Scan.chunk_sound context_valid facts instructions 100352 1024
    h100352 checked_100352
  have h102400 := Scan.chunk_sound context_valid facts instructions 101376 1024
    h101376 checked_101376
  have h103424 := Scan.chunk_sound context_valid facts instructions 102400 1024
    h102400 checked_102400
  have h104448 := Scan.chunk_sound context_valid facts instructions 103424 1024
    h103424 checked_103424
  have h105472 := Scan.chunk_sound context_valid facts instructions 104448 1024
    h104448 checked_104448
  have h106496 := Scan.chunk_sound context_valid facts instructions 105472 1024
    h105472 checked_105472
  have h107520 := Scan.chunk_sound context_valid facts instructions 106496 1024
    h106496 checked_106496
  have h108544 := Scan.chunk_sound context_valid facts instructions 107520 1024
    h107520 checked_107520
  have h109568 := Scan.chunk_sound context_valid facts instructions 108544 1024
    h108544 checked_108544
  have h110592 := Scan.chunk_sound context_valid facts instructions 109568 1024
    h109568 checked_109568
  have h111616 := Scan.chunk_sound context_valid facts instructions 110592 1024
    h110592 checked_110592
  have h112640 := Scan.chunk_sound context_valid facts instructions 111616 1024
    h111616 checked_111616
  have h113664 := Scan.chunk_sound context_valid facts instructions 112640 1024
    h112640 checked_112640
  have h114688 := Scan.chunk_sound context_valid facts instructions 113664 1024
    h113664 checked_113664
  exact h114688

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
