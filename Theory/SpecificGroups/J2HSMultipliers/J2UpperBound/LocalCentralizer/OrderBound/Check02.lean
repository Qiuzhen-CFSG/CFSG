module

public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound.Tables

/-! Kernel-checked deductions for the literal normalized J₂ centralizer presentation.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
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
theorem checked_40960 : Scan.checkChunk context facts instructions 40960 165 = true := by
  decide +kernel

theorem sound_32768 (prior : ∀ n, n < 32768 →
    Holds (⊥ : Subgroup Presentation) generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 41125 → Holds (⊥ : Subgroup Presentation) generator (definitions.repr generator) (facts n) := by
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
  have h41125 := Scan.chunk_sound context_valid facts instructions 40960 165
    h40960 checked_40960
  exact h41125

end Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
