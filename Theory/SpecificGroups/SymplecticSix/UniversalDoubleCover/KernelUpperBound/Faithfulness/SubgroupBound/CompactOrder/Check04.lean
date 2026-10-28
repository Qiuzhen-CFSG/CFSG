module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.SubgroupBound.CompactOrder.Tables

/-! Kernel-checked deductions for the literal compact ATLAS S62G1-P1 subgroup presentation.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound.CompactOrder
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_65536 : Scan.checkChunk context facts instructions 65536 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_66560 : Scan.checkChunk context facts instructions 66560 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_67584 : Scan.checkChunk context facts instructions 67584 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_68608 : Scan.checkChunk context facts instructions 68608 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_69632 : Scan.checkChunk context facts instructions 69632 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_70656 : Scan.checkChunk context facts instructions 70656 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_71680 : Scan.checkChunk context facts instructions 71680 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_72704 : Scan.checkChunk context facts instructions 72704 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_73728 : Scan.checkChunk context facts instructions 73728 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_74752 : Scan.checkChunk context facts instructions 74752 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_75776 : Scan.checkChunk context facts instructions 75776 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_76800 : Scan.checkChunk context facts instructions 76800 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_77824 : Scan.checkChunk context facts instructions 77824 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_78848 : Scan.checkChunk context facts instructions 78848 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_79872 : Scan.checkChunk context facts instructions 79872 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_80896 : Scan.checkChunk context facts instructions 80896 1024 = true := by
  decide +kernel

theorem sound_65536 (prior : ∀ n, n < 65536 →
    Holds smallSubgroup generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 81920 → Holds smallSubgroup generator (definitions.repr generator) (facts n) := by
  have h66560 := Scan.chunk_sound context_valid facts instructions 65536 1024
    prior checked_65536
  have h67584 := Scan.chunk_sound context_valid facts instructions 66560 1024
    h66560 checked_66560
  have h68608 := Scan.chunk_sound context_valid facts instructions 67584 1024
    h67584 checked_67584
  have h69632 := Scan.chunk_sound context_valid facts instructions 68608 1024
    h68608 checked_68608
  have h70656 := Scan.chunk_sound context_valid facts instructions 69632 1024
    h69632 checked_69632
  have h71680 := Scan.chunk_sound context_valid facts instructions 70656 1024
    h70656 checked_70656
  have h72704 := Scan.chunk_sound context_valid facts instructions 71680 1024
    h71680 checked_71680
  have h73728 := Scan.chunk_sound context_valid facts instructions 72704 1024
    h72704 checked_72704
  have h74752 := Scan.chunk_sound context_valid facts instructions 73728 1024
    h73728 checked_73728
  have h75776 := Scan.chunk_sound context_valid facts instructions 74752 1024
    h74752 checked_74752
  have h76800 := Scan.chunk_sound context_valid facts instructions 75776 1024
    h75776 checked_75776
  have h77824 := Scan.chunk_sound context_valid facts instructions 76800 1024
    h76800 checked_76800
  have h78848 := Scan.chunk_sound context_valid facts instructions 77824 1024
    h77824 checked_77824
  have h79872 := Scan.chunk_sound context_valid facts instructions 78848 1024
    h78848 checked_78848
  have h80896 := Scan.chunk_sound context_valid facts instructions 79872 1024
    h79872 checked_79872
  have h81920 := Scan.chunk_sound context_valid facts instructions 80896 1024
    h80896 checked_80896
  exact h81920

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound.CompactOrder
