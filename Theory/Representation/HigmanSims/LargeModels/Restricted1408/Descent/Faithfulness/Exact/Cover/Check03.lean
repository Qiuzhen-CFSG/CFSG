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
theorem checked_49152 : Scan.checkChunk context facts instructions 49152 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_49664 : Scan.checkChunk context facts instructions 49664 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_50176 : Scan.checkChunk context facts instructions 50176 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_50688 : Scan.checkChunk context facts instructions 50688 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_51200 : Scan.checkChunk context facts instructions 51200 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_51712 : Scan.checkChunk context facts instructions 51712 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_52224 : Scan.checkChunk context facts instructions 52224 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_52736 : Scan.checkChunk context facts instructions 52736 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_53248 : Scan.checkChunk context facts instructions 53248 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_53760 : Scan.checkChunk context facts instructions 53760 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_54272 : Scan.checkChunk context facts instructions 54272 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_54784 : Scan.checkChunk context facts instructions 54784 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_55296 : Scan.checkChunk context facts instructions 55296 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_55808 : Scan.checkChunk context facts instructions 55808 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_56320 : Scan.checkChunk context facts instructions 56320 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_56832 : Scan.checkChunk context facts instructions 56832 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_57344 : Scan.checkChunk context facts instructions 57344 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_57856 : Scan.checkChunk context facts instructions 57856 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_58368 : Scan.checkChunk context facts instructions 58368 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_58880 : Scan.checkChunk context facts instructions 58880 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_59392 : Scan.checkChunk context facts instructions 59392 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_59904 : Scan.checkChunk context facts instructions 59904 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_60416 : Scan.checkChunk context facts instructions 60416 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_60928 : Scan.checkChunk context facts instructions 60928 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_61440 : Scan.checkChunk context facts instructions 61440 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_61952 : Scan.checkChunk context facts instructions 61952 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_62464 : Scan.checkChunk context facts instructions 62464 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_62976 : Scan.checkChunk context facts instructions 62976 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_63488 : Scan.checkChunk context facts instructions 63488 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_64000 : Scan.checkChunk context facts instructions 64000 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_64512 : Scan.checkChunk context facts instructions 64512 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_65024 : Scan.checkChunk context facts instructions 65024 512 = true := by
  decide +kernel

theorem all_hold_65536 (prior : ∀ n, n < 49152 → Holds centralizer certGenerator (definitions.repr certGenerator) (facts n)) : ∀ n, n < 65536 →
    Holds centralizer certGenerator (definitions.repr certGenerator) (facts n) := by
  have h49664 := Scan.chunk_sound context_valid facts instructions 49152 512
    prior checked_49152
  have h50176 := Scan.chunk_sound context_valid facts instructions 49664 512
    h49664 checked_49664
  have h50688 := Scan.chunk_sound context_valid facts instructions 50176 512
    h50176 checked_50176
  have h51200 := Scan.chunk_sound context_valid facts instructions 50688 512
    h50688 checked_50688
  have h51712 := Scan.chunk_sound context_valid facts instructions 51200 512
    h51200 checked_51200
  have h52224 := Scan.chunk_sound context_valid facts instructions 51712 512
    h51712 checked_51712
  have h52736 := Scan.chunk_sound context_valid facts instructions 52224 512
    h52224 checked_52224
  have h53248 := Scan.chunk_sound context_valid facts instructions 52736 512
    h52736 checked_52736
  have h53760 := Scan.chunk_sound context_valid facts instructions 53248 512
    h53248 checked_53248
  have h54272 := Scan.chunk_sound context_valid facts instructions 53760 512
    h53760 checked_53760
  have h54784 := Scan.chunk_sound context_valid facts instructions 54272 512
    h54272 checked_54272
  have h55296 := Scan.chunk_sound context_valid facts instructions 54784 512
    h54784 checked_54784
  have h55808 := Scan.chunk_sound context_valid facts instructions 55296 512
    h55296 checked_55296
  have h56320 := Scan.chunk_sound context_valid facts instructions 55808 512
    h55808 checked_55808
  have h56832 := Scan.chunk_sound context_valid facts instructions 56320 512
    h56320 checked_56320
  have h57344 := Scan.chunk_sound context_valid facts instructions 56832 512
    h56832 checked_56832
  have h57856 := Scan.chunk_sound context_valid facts instructions 57344 512
    h57344 checked_57344
  have h58368 := Scan.chunk_sound context_valid facts instructions 57856 512
    h57856 checked_57856
  have h58880 := Scan.chunk_sound context_valid facts instructions 58368 512
    h58368 checked_58368
  have h59392 := Scan.chunk_sound context_valid facts instructions 58880 512
    h58880 checked_58880
  have h59904 := Scan.chunk_sound context_valid facts instructions 59392 512
    h59392 checked_59392
  have h60416 := Scan.chunk_sound context_valid facts instructions 59904 512
    h59904 checked_59904
  have h60928 := Scan.chunk_sound context_valid facts instructions 60416 512
    h60416 checked_60416
  have h61440 := Scan.chunk_sound context_valid facts instructions 60928 512
    h60928 checked_60928
  have h61952 := Scan.chunk_sound context_valid facts instructions 61440 512
    h61440 checked_61440
  have h62464 := Scan.chunk_sound context_valid facts instructions 61952 512
    h61952 checked_61952
  have h62976 := Scan.chunk_sound context_valid facts instructions 62464 512
    h62464 checked_62464
  have h63488 := Scan.chunk_sound context_valid facts instructions 62976 512
    h62976 checked_62976
  have h64000 := Scan.chunk_sound context_valid facts instructions 63488 512
    h63488 checked_63488
  have h64512 := Scan.chunk_sound context_valid facts instructions 64000 512
    h64000 checked_64000
  have h65024 := Scan.chunk_sound context_valid facts instructions 64512 512
    h64512 checked_64512
  have h65536 := Scan.chunk_sound context_valid facts instructions 65024 512
    h65024 checked_65024
  exact h65536

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
