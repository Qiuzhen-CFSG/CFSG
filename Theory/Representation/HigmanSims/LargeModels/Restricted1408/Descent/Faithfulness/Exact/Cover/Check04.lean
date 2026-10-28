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
theorem checked_65536 : Scan.checkChunk context facts instructions 65536 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_66048 : Scan.checkChunk context facts instructions 66048 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_66560 : Scan.checkChunk context facts instructions 66560 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_67072 : Scan.checkChunk context facts instructions 67072 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_67584 : Scan.checkChunk context facts instructions 67584 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_68096 : Scan.checkChunk context facts instructions 68096 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_68608 : Scan.checkChunk context facts instructions 68608 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_69120 : Scan.checkChunk context facts instructions 69120 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_69632 : Scan.checkChunk context facts instructions 69632 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_70144 : Scan.checkChunk context facts instructions 70144 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_70656 : Scan.checkChunk context facts instructions 70656 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_71168 : Scan.checkChunk context facts instructions 71168 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_71680 : Scan.checkChunk context facts instructions 71680 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_72192 : Scan.checkChunk context facts instructions 72192 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_72704 : Scan.checkChunk context facts instructions 72704 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_73216 : Scan.checkChunk context facts instructions 73216 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_73728 : Scan.checkChunk context facts instructions 73728 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_74240 : Scan.checkChunk context facts instructions 74240 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_74752 : Scan.checkChunk context facts instructions 74752 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_75264 : Scan.checkChunk context facts instructions 75264 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_75776 : Scan.checkChunk context facts instructions 75776 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_76288 : Scan.checkChunk context facts instructions 76288 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_76800 : Scan.checkChunk context facts instructions 76800 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_77312 : Scan.checkChunk context facts instructions 77312 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_77824 : Scan.checkChunk context facts instructions 77824 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_78336 : Scan.checkChunk context facts instructions 78336 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_78848 : Scan.checkChunk context facts instructions 78848 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_79360 : Scan.checkChunk context facts instructions 79360 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_79872 : Scan.checkChunk context facts instructions 79872 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_80384 : Scan.checkChunk context facts instructions 80384 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_80896 : Scan.checkChunk context facts instructions 80896 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_81408 : Scan.checkChunk context facts instructions 81408 512 = true := by
  decide +kernel

theorem all_hold_81920 (prior : ∀ n, n < 65536 → Holds centralizer certGenerator (definitions.repr certGenerator) (facts n)) : ∀ n, n < 81920 →
    Holds centralizer certGenerator (definitions.repr certGenerator) (facts n) := by
  have h66048 := Scan.chunk_sound context_valid facts instructions 65536 512
    prior checked_65536
  have h66560 := Scan.chunk_sound context_valid facts instructions 66048 512
    h66048 checked_66048
  have h67072 := Scan.chunk_sound context_valid facts instructions 66560 512
    h66560 checked_66560
  have h67584 := Scan.chunk_sound context_valid facts instructions 67072 512
    h67072 checked_67072
  have h68096 := Scan.chunk_sound context_valid facts instructions 67584 512
    h67584 checked_67584
  have h68608 := Scan.chunk_sound context_valid facts instructions 68096 512
    h68096 checked_68096
  have h69120 := Scan.chunk_sound context_valid facts instructions 68608 512
    h68608 checked_68608
  have h69632 := Scan.chunk_sound context_valid facts instructions 69120 512
    h69120 checked_69120
  have h70144 := Scan.chunk_sound context_valid facts instructions 69632 512
    h69632 checked_69632
  have h70656 := Scan.chunk_sound context_valid facts instructions 70144 512
    h70144 checked_70144
  have h71168 := Scan.chunk_sound context_valid facts instructions 70656 512
    h70656 checked_70656
  have h71680 := Scan.chunk_sound context_valid facts instructions 71168 512
    h71168 checked_71168
  have h72192 := Scan.chunk_sound context_valid facts instructions 71680 512
    h71680 checked_71680
  have h72704 := Scan.chunk_sound context_valid facts instructions 72192 512
    h72192 checked_72192
  have h73216 := Scan.chunk_sound context_valid facts instructions 72704 512
    h72704 checked_72704
  have h73728 := Scan.chunk_sound context_valid facts instructions 73216 512
    h73216 checked_73216
  have h74240 := Scan.chunk_sound context_valid facts instructions 73728 512
    h73728 checked_73728
  have h74752 := Scan.chunk_sound context_valid facts instructions 74240 512
    h74240 checked_74240
  have h75264 := Scan.chunk_sound context_valid facts instructions 74752 512
    h74752 checked_74752
  have h75776 := Scan.chunk_sound context_valid facts instructions 75264 512
    h75264 checked_75264
  have h76288 := Scan.chunk_sound context_valid facts instructions 75776 512
    h75776 checked_75776
  have h76800 := Scan.chunk_sound context_valid facts instructions 76288 512
    h76288 checked_76288
  have h77312 := Scan.chunk_sound context_valid facts instructions 76800 512
    h76800 checked_76800
  have h77824 := Scan.chunk_sound context_valid facts instructions 77312 512
    h77312 checked_77312
  have h78336 := Scan.chunk_sound context_valid facts instructions 77824 512
    h77824 checked_77824
  have h78848 := Scan.chunk_sound context_valid facts instructions 78336 512
    h78336 checked_78336
  have h79360 := Scan.chunk_sound context_valid facts instructions 78848 512
    h78848 checked_78848
  have h79872 := Scan.chunk_sound context_valid facts instructions 79360 512
    h79360 checked_79360
  have h80384 := Scan.chunk_sound context_valid facts instructions 79872 512
    h79872 checked_79872
  have h80896 := Scan.chunk_sound context_valid facts instructions 80384 512
    h80384 checked_80384
  have h81408 := Scan.chunk_sound context_valid facts instructions 80896 512
    h80896 checked_80896
  have h81920 := Scan.chunk_sound context_valid facts instructions 81408 512
    h81408 checked_81408
  exact h81920

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
