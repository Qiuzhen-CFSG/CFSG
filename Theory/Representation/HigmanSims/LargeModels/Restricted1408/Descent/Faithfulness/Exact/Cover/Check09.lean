module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Tables

/-! Centralizer-coset certificate for the thirteen ATLAS HS relators.
Untrusted data generated from the retained trace; all deduction checks use
Lean's kernel and the actual abstract relations. See `source/README.md`. -/

public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_147456 : Scan.checkChunk context facts instructions 147456 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_147968 : Scan.checkChunk context facts instructions 147968 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_148480 : Scan.checkChunk context facts instructions 148480 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_148992 : Scan.checkChunk context facts instructions 148992 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_149504 : Scan.checkChunk context facts instructions 149504 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_150016 : Scan.checkChunk context facts instructions 150016 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_150528 : Scan.checkChunk context facts instructions 150528 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_151040 : Scan.checkChunk context facts instructions 151040 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_151552 : Scan.checkChunk context facts instructions 151552 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_152064 : Scan.checkChunk context facts instructions 152064 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_152576 : Scan.checkChunk context facts instructions 152576 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_153088 : Scan.checkChunk context facts instructions 153088 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_153600 : Scan.checkChunk context facts instructions 153600 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_154112 : Scan.checkChunk context facts instructions 154112 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_154624 : Scan.checkChunk context facts instructions 154624 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_155136 : Scan.checkChunk context facts instructions 155136 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_155648 : Scan.checkChunk context facts instructions 155648 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_156160 : Scan.checkChunk context facts instructions 156160 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_156672 : Scan.checkChunk context facts instructions 156672 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_157184 : Scan.checkChunk context facts instructions 157184 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_157696 : Scan.checkChunk context facts instructions 157696 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_158208 : Scan.checkChunk context facts instructions 158208 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_158720 : Scan.checkChunk context facts instructions 158720 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_159232 : Scan.checkChunk context facts instructions 159232 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_159744 : Scan.checkChunk context facts instructions 159744 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_160256 : Scan.checkChunk context facts instructions 160256 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_160768 : Scan.checkChunk context facts instructions 160768 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_161280 : Scan.checkChunk context facts instructions 161280 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_161792 : Scan.checkChunk context facts instructions 161792 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_162304 : Scan.checkChunk context facts instructions 162304 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_162816 : Scan.checkChunk context facts instructions 162816 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_163328 : Scan.checkChunk context facts instructions 163328 512 = true := by
  decide +kernel

theorem all_hold_163840 (prior : ∀ n, n < 147456 → Holds centralizer certGenerator (definitions.repr certGenerator) (facts n)) : ∀ n, n < 163840 →
    Holds centralizer certGenerator (definitions.repr certGenerator) (facts n) := by
  have h147968 := Scan.chunk_sound context_valid facts instructions 147456 512
    prior checked_147456
  have h148480 := Scan.chunk_sound context_valid facts instructions 147968 512
    h147968 checked_147968
  have h148992 := Scan.chunk_sound context_valid facts instructions 148480 512
    h148480 checked_148480
  have h149504 := Scan.chunk_sound context_valid facts instructions 148992 512
    h148992 checked_148992
  have h150016 := Scan.chunk_sound context_valid facts instructions 149504 512
    h149504 checked_149504
  have h150528 := Scan.chunk_sound context_valid facts instructions 150016 512
    h150016 checked_150016
  have h151040 := Scan.chunk_sound context_valid facts instructions 150528 512
    h150528 checked_150528
  have h151552 := Scan.chunk_sound context_valid facts instructions 151040 512
    h151040 checked_151040
  have h152064 := Scan.chunk_sound context_valid facts instructions 151552 512
    h151552 checked_151552
  have h152576 := Scan.chunk_sound context_valid facts instructions 152064 512
    h152064 checked_152064
  have h153088 := Scan.chunk_sound context_valid facts instructions 152576 512
    h152576 checked_152576
  have h153600 := Scan.chunk_sound context_valid facts instructions 153088 512
    h153088 checked_153088
  have h154112 := Scan.chunk_sound context_valid facts instructions 153600 512
    h153600 checked_153600
  have h154624 := Scan.chunk_sound context_valid facts instructions 154112 512
    h154112 checked_154112
  have h155136 := Scan.chunk_sound context_valid facts instructions 154624 512
    h154624 checked_154624
  have h155648 := Scan.chunk_sound context_valid facts instructions 155136 512
    h155136 checked_155136
  have h156160 := Scan.chunk_sound context_valid facts instructions 155648 512
    h155648 checked_155648
  have h156672 := Scan.chunk_sound context_valid facts instructions 156160 512
    h156160 checked_156160
  have h157184 := Scan.chunk_sound context_valid facts instructions 156672 512
    h156672 checked_156672
  have h157696 := Scan.chunk_sound context_valid facts instructions 157184 512
    h157184 checked_157184
  have h158208 := Scan.chunk_sound context_valid facts instructions 157696 512
    h157696 checked_157696
  have h158720 := Scan.chunk_sound context_valid facts instructions 158208 512
    h158208 checked_158208
  have h159232 := Scan.chunk_sound context_valid facts instructions 158720 512
    h158720 checked_158720
  have h159744 := Scan.chunk_sound context_valid facts instructions 159232 512
    h159232 checked_159232
  have h160256 := Scan.chunk_sound context_valid facts instructions 159744 512
    h159744 checked_159744
  have h160768 := Scan.chunk_sound context_valid facts instructions 160256 512
    h160256 checked_160256
  have h161280 := Scan.chunk_sound context_valid facts instructions 160768 512
    h160768 checked_160768
  have h161792 := Scan.chunk_sound context_valid facts instructions 161280 512
    h161280 checked_161280
  have h162304 := Scan.chunk_sound context_valid facts instructions 161792 512
    h161792 checked_161792
  have h162816 := Scan.chunk_sound context_valid facts instructions 162304 512
    h162304 checked_162304
  have h163328 := Scan.chunk_sound context_valid facts instructions 162816 512
    h162816 checked_162816
  have h163840 := Scan.chunk_sound context_valid facts instructions 163328 512
    h163328 checked_163328
  exact h163840

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
