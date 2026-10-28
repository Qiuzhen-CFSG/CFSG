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
theorem checked_81920 : Scan.checkChunk context facts instructions 81920 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_82432 : Scan.checkChunk context facts instructions 82432 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_82944 : Scan.checkChunk context facts instructions 82944 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_83456 : Scan.checkChunk context facts instructions 83456 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_83968 : Scan.checkChunk context facts instructions 83968 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_84480 : Scan.checkChunk context facts instructions 84480 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_84992 : Scan.checkChunk context facts instructions 84992 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_85504 : Scan.checkChunk context facts instructions 85504 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_86016 : Scan.checkChunk context facts instructions 86016 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_86528 : Scan.checkChunk context facts instructions 86528 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_87040 : Scan.checkChunk context facts instructions 87040 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_87552 : Scan.checkChunk context facts instructions 87552 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_88064 : Scan.checkChunk context facts instructions 88064 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_88576 : Scan.checkChunk context facts instructions 88576 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_89088 : Scan.checkChunk context facts instructions 89088 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_89600 : Scan.checkChunk context facts instructions 89600 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_90112 : Scan.checkChunk context facts instructions 90112 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_90624 : Scan.checkChunk context facts instructions 90624 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_91136 : Scan.checkChunk context facts instructions 91136 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_91648 : Scan.checkChunk context facts instructions 91648 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_92160 : Scan.checkChunk context facts instructions 92160 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_92672 : Scan.checkChunk context facts instructions 92672 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_93184 : Scan.checkChunk context facts instructions 93184 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_93696 : Scan.checkChunk context facts instructions 93696 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_94208 : Scan.checkChunk context facts instructions 94208 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_94720 : Scan.checkChunk context facts instructions 94720 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_95232 : Scan.checkChunk context facts instructions 95232 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_95744 : Scan.checkChunk context facts instructions 95744 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_96256 : Scan.checkChunk context facts instructions 96256 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_96768 : Scan.checkChunk context facts instructions 96768 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_97280 : Scan.checkChunk context facts instructions 97280 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_97792 : Scan.checkChunk context facts instructions 97792 512 = true := by
  decide +kernel

theorem all_hold_98304 (prior : ∀ n, n < 81920 → Holds centralizer certGenerator (definitions.repr certGenerator) (facts n)) : ∀ n, n < 98304 →
    Holds centralizer certGenerator (definitions.repr certGenerator) (facts n) := by
  have h82432 := Scan.chunk_sound context_valid facts instructions 81920 512
    prior checked_81920
  have h82944 := Scan.chunk_sound context_valid facts instructions 82432 512
    h82432 checked_82432
  have h83456 := Scan.chunk_sound context_valid facts instructions 82944 512
    h82944 checked_82944
  have h83968 := Scan.chunk_sound context_valid facts instructions 83456 512
    h83456 checked_83456
  have h84480 := Scan.chunk_sound context_valid facts instructions 83968 512
    h83968 checked_83968
  have h84992 := Scan.chunk_sound context_valid facts instructions 84480 512
    h84480 checked_84480
  have h85504 := Scan.chunk_sound context_valid facts instructions 84992 512
    h84992 checked_84992
  have h86016 := Scan.chunk_sound context_valid facts instructions 85504 512
    h85504 checked_85504
  have h86528 := Scan.chunk_sound context_valid facts instructions 86016 512
    h86016 checked_86016
  have h87040 := Scan.chunk_sound context_valid facts instructions 86528 512
    h86528 checked_86528
  have h87552 := Scan.chunk_sound context_valid facts instructions 87040 512
    h87040 checked_87040
  have h88064 := Scan.chunk_sound context_valid facts instructions 87552 512
    h87552 checked_87552
  have h88576 := Scan.chunk_sound context_valid facts instructions 88064 512
    h88064 checked_88064
  have h89088 := Scan.chunk_sound context_valid facts instructions 88576 512
    h88576 checked_88576
  have h89600 := Scan.chunk_sound context_valid facts instructions 89088 512
    h89088 checked_89088
  have h90112 := Scan.chunk_sound context_valid facts instructions 89600 512
    h89600 checked_89600
  have h90624 := Scan.chunk_sound context_valid facts instructions 90112 512
    h90112 checked_90112
  have h91136 := Scan.chunk_sound context_valid facts instructions 90624 512
    h90624 checked_90624
  have h91648 := Scan.chunk_sound context_valid facts instructions 91136 512
    h91136 checked_91136
  have h92160 := Scan.chunk_sound context_valid facts instructions 91648 512
    h91648 checked_91648
  have h92672 := Scan.chunk_sound context_valid facts instructions 92160 512
    h92160 checked_92160
  have h93184 := Scan.chunk_sound context_valid facts instructions 92672 512
    h92672 checked_92672
  have h93696 := Scan.chunk_sound context_valid facts instructions 93184 512
    h93184 checked_93184
  have h94208 := Scan.chunk_sound context_valid facts instructions 93696 512
    h93696 checked_93696
  have h94720 := Scan.chunk_sound context_valid facts instructions 94208 512
    h94208 checked_94208
  have h95232 := Scan.chunk_sound context_valid facts instructions 94720 512
    h94720 checked_94720
  have h95744 := Scan.chunk_sound context_valid facts instructions 95232 512
    h95232 checked_95232
  have h96256 := Scan.chunk_sound context_valid facts instructions 95744 512
    h95744 checked_95744
  have h96768 := Scan.chunk_sound context_valid facts instructions 96256 512
    h96256 checked_96256
  have h97280 := Scan.chunk_sound context_valid facts instructions 96768 512
    h96768 checked_96768
  have h97792 := Scan.chunk_sound context_valid facts instructions 97280 512
    h97280 checked_97280
  have h98304 := Scan.chunk_sound context_valid facts instructions 97792 512
    h97792 checked_97792
  exact h98304

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
