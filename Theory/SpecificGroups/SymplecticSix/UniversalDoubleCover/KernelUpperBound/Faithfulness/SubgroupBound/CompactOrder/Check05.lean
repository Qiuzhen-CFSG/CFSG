module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.SubgroupBound.CompactOrder.Tables

/-! Kernel-checked deductions for the literal compact ATLAS S62G1-P1 subgroup presentation.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound.CompactOrder
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_81920 : Scan.checkChunk context facts instructions 81920 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_82944 : Scan.checkChunk context facts instructions 82944 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_83968 : Scan.checkChunk context facts instructions 83968 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_84992 : Scan.checkChunk context facts instructions 84992 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_86016 : Scan.checkChunk context facts instructions 86016 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_87040 : Scan.checkChunk context facts instructions 87040 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_88064 : Scan.checkChunk context facts instructions 88064 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_89088 : Scan.checkChunk context facts instructions 89088 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_90112 : Scan.checkChunk context facts instructions 90112 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_91136 : Scan.checkChunk context facts instructions 91136 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_92160 : Scan.checkChunk context facts instructions 92160 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_93184 : Scan.checkChunk context facts instructions 93184 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_94208 : Scan.checkChunk context facts instructions 94208 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_95232 : Scan.checkChunk context facts instructions 95232 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_96256 : Scan.checkChunk context facts instructions 96256 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_97280 : Scan.checkChunk context facts instructions 97280 1024 = true := by
  decide +kernel

theorem sound_81920 (prior : ∀ n, n < 81920 →
    Holds smallSubgroup generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 98304 → Holds smallSubgroup generator (definitions.repr generator) (facts n) := by
  have h82944 := Scan.chunk_sound context_valid facts instructions 81920 1024
    prior checked_81920
  have h83968 := Scan.chunk_sound context_valid facts instructions 82944 1024
    h82944 checked_82944
  have h84992 := Scan.chunk_sound context_valid facts instructions 83968 1024
    h83968 checked_83968
  have h86016 := Scan.chunk_sound context_valid facts instructions 84992 1024
    h84992 checked_84992
  have h87040 := Scan.chunk_sound context_valid facts instructions 86016 1024
    h86016 checked_86016
  have h88064 := Scan.chunk_sound context_valid facts instructions 87040 1024
    h87040 checked_87040
  have h89088 := Scan.chunk_sound context_valid facts instructions 88064 1024
    h88064 checked_88064
  have h90112 := Scan.chunk_sound context_valid facts instructions 89088 1024
    h89088 checked_89088
  have h91136 := Scan.chunk_sound context_valid facts instructions 90112 1024
    h90112 checked_90112
  have h92160 := Scan.chunk_sound context_valid facts instructions 91136 1024
    h91136 checked_91136
  have h93184 := Scan.chunk_sound context_valid facts instructions 92160 1024
    h92160 checked_92160
  have h94208 := Scan.chunk_sound context_valid facts instructions 93184 1024
    h93184 checked_93184
  have h95232 := Scan.chunk_sound context_valid facts instructions 94208 1024
    h94208 checked_94208
  have h96256 := Scan.chunk_sound context_valid facts instructions 95232 1024
    h95232 checked_95232
  have h97280 := Scan.chunk_sound context_valid facts instructions 96256 1024
    h96256 checked_96256
  have h98304 := Scan.chunk_sound context_valid facts instructions 97280 1024
    h97280 checked_97280
  exact h98304

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound.CompactOrder
