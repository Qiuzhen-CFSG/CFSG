module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Tables

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_147456 : Scan.checkChunk context facts instructions 147456 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_148480 : Scan.checkChunk context facts instructions 148480 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_149504 : Scan.checkChunk context facts instructions 149504 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_150528 : Scan.checkChunk context facts instructions 150528 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_151552 : Scan.checkChunk context facts instructions 151552 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_152576 : Scan.checkChunk context facts instructions 152576 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_153600 : Scan.checkChunk context facts instructions 153600 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_154624 : Scan.checkChunk context facts instructions 154624 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_155648 : Scan.checkChunk context facts instructions 155648 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_156672 : Scan.checkChunk context facts instructions 156672 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_157696 : Scan.checkChunk context facts instructions 157696 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_158720 : Scan.checkChunk context facts instructions 158720 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_159744 : Scan.checkChunk context facts instructions 159744 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_160768 : Scan.checkChunk context facts instructions 160768 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_161792 : Scan.checkChunk context facts instructions 161792 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_162816 : Scan.checkChunk context facts instructions 162816 1024 = true := by
  decide +kernel

theorem sound_147456 (prior : ∀ n, n < 147456 →
    Holds M1 generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 163840 → Holds M1 generator (definitions.repr generator) (facts n) := by
  have h148480 := Scan.chunk_sound context_valid facts instructions 147456 1024
    prior checked_147456
  have h149504 := Scan.chunk_sound context_valid facts instructions 148480 1024
    h148480 checked_148480
  have h150528 := Scan.chunk_sound context_valid facts instructions 149504 1024
    h149504 checked_149504
  have h151552 := Scan.chunk_sound context_valid facts instructions 150528 1024
    h150528 checked_150528
  have h152576 := Scan.chunk_sound context_valid facts instructions 151552 1024
    h151552 checked_151552
  have h153600 := Scan.chunk_sound context_valid facts instructions 152576 1024
    h152576 checked_152576
  have h154624 := Scan.chunk_sound context_valid facts instructions 153600 1024
    h153600 checked_153600
  have h155648 := Scan.chunk_sound context_valid facts instructions 154624 1024
    h154624 checked_154624
  have h156672 := Scan.chunk_sound context_valid facts instructions 155648 1024
    h155648 checked_155648
  have h157696 := Scan.chunk_sound context_valid facts instructions 156672 1024
    h156672 checked_156672
  have h158720 := Scan.chunk_sound context_valid facts instructions 157696 1024
    h157696 checked_157696
  have h159744 := Scan.chunk_sound context_valid facts instructions 158720 1024
    h158720 checked_158720
  have h160768 := Scan.chunk_sound context_valid facts instructions 159744 1024
    h159744 checked_159744
  have h161792 := Scan.chunk_sound context_valid facts instructions 160768 1024
    h160768 checked_160768
  have h162816 := Scan.chunk_sound context_valid facts instructions 161792 1024
    h161792 checked_161792
  have h163840 := Scan.chunk_sound context_valid facts instructions 162816 1024
    h162816 checked_162816
  exact h163840

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
