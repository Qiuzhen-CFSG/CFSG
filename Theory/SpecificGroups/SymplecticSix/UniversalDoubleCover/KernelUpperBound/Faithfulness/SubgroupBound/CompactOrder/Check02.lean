module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.SubgroupBound.CompactOrder.Tables

/-! Kernel-checked deductions for the literal compact ATLAS S62G1-P1 subgroup presentation.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound.CompactOrder
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_32768 : Scan.checkChunk context facts instructions 32768 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_33792 : Scan.checkChunk context facts instructions 33792 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_34816 : Scan.checkChunk context facts instructions 34816 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_35840 : Scan.checkChunk context facts instructions 35840 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_36864 : Scan.checkChunk context facts instructions 36864 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_37888 : Scan.checkChunk context facts instructions 37888 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_38912 : Scan.checkChunk context facts instructions 38912 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_39936 : Scan.checkChunk context facts instructions 39936 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_40960 : Scan.checkChunk context facts instructions 40960 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_41984 : Scan.checkChunk context facts instructions 41984 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_43008 : Scan.checkChunk context facts instructions 43008 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_44032 : Scan.checkChunk context facts instructions 44032 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_45056 : Scan.checkChunk context facts instructions 45056 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_46080 : Scan.checkChunk context facts instructions 46080 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_47104 : Scan.checkChunk context facts instructions 47104 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_48128 : Scan.checkChunk context facts instructions 48128 1024 = true := by
  decide +kernel

theorem sound_32768 (prior : ∀ n, n < 32768 →
    Holds smallSubgroup generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 49152 → Holds smallSubgroup generator (definitions.repr generator) (facts n) := by
  have h33792 := Scan.chunk_sound context_valid facts instructions 32768 1024
    prior checked_32768
  have h34816 := Scan.chunk_sound context_valid facts instructions 33792 1024
    h33792 checked_33792
  have h35840 := Scan.chunk_sound context_valid facts instructions 34816 1024
    h34816 checked_34816
  have h36864 := Scan.chunk_sound context_valid facts instructions 35840 1024
    h35840 checked_35840
  have h37888 := Scan.chunk_sound context_valid facts instructions 36864 1024
    h36864 checked_36864
  have h38912 := Scan.chunk_sound context_valid facts instructions 37888 1024
    h37888 checked_37888
  have h39936 := Scan.chunk_sound context_valid facts instructions 38912 1024
    h38912 checked_38912
  have h40960 := Scan.chunk_sound context_valid facts instructions 39936 1024
    h39936 checked_39936
  have h41984 := Scan.chunk_sound context_valid facts instructions 40960 1024
    h40960 checked_40960
  have h43008 := Scan.chunk_sound context_valid facts instructions 41984 1024
    h41984 checked_41984
  have h44032 := Scan.chunk_sound context_valid facts instructions 43008 1024
    h43008 checked_43008
  have h45056 := Scan.chunk_sound context_valid facts instructions 44032 1024
    h44032 checked_44032
  have h46080 := Scan.chunk_sound context_valid facts instructions 45056 1024
    h45056 checked_45056
  have h47104 := Scan.chunk_sound context_valid facts instructions 46080 1024
    h46080 checked_46080
  have h48128 := Scan.chunk_sound context_valid facts instructions 47104 1024
    h47104 checked_47104
  have h49152 := Scan.chunk_sound context_valid facts instructions 48128 1024
    h48128 checked_48128
  exact h49152

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound.CompactOrder
