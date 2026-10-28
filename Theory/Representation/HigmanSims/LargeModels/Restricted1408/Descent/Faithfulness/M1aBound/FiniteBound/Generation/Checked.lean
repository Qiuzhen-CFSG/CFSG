module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Generation.Data

/-! Checked generation of the exact HS Schreier presentation by its first three
generators. Source: the literal 1,300 Schreier relators; see source/README.md.
The untrusted trace supplies only six-rule deductions and relator scans. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier
open Subgroup.CosetWordCertificate

namespace GenerationCertificate

theorem checked_0 : allBlock stepCheck 7 0 = true := by decide +kernel

theorem checked_128 : allBlock stepCheck 7 128 = true := by decide +kernel

theorem checked_256 : allBlock stepCheck 7 256 = true := by decide +kernel

theorem checked_384 : allBlock stepCheck 7 384 = true := by decide +kernel

theorem checked_512 : allBlock stepCheck 7 512 = true := by decide +kernel

theorem checked_640 : allBlock stepCheck 7 640 = true := by decide +kernel

theorem checked_768 : allBlock stepCheck 7 768 = true := by decide +kernel

theorem checked_896 : allBlock stepCheck 7 896 = true := by decide +kernel

theorem checked_1024 : allBlock stepCheck 7 1024 = true := by decide +kernel

theorem checked_1152 : allBlock stepCheck 7 1152 = true := by decide +kernel

theorem checked_1280 : allBlock stepCheck 7 1280 = true := by decide +kernel

theorem checked_1408 : allBlock stepCheck 7 1408 = true := by decide +kernel

theorem checked_1536 : allBlock stepCheck 7 1536 = true := by decide +kernel

theorem checked_1664 : allBlock stepCheck 7 1664 = true := by decide +kernel

theorem checked_1792 : allBlock stepCheck 7 1792 = true := by decide +kernel

theorem checked_1920 : allBlock stepCheck 7 1920 = true := by decide +kernel

theorem checked_2048 : allBlock stepCheck 7 2048 = true := by decide +kernel

theorem checked_2176 : allBlock stepCheck 7 2176 = true := by decide +kernel

theorem checked_2304 : allBlock stepCheck 7 2304 = true := by decide +kernel

theorem checked_2432 : allBlock stepCheck 7 2432 = true := by decide +kernel

theorem checked_2560 : allBlock stepCheck 7 2560 = true := by decide +kernel

theorem checked_2688 : allBlock stepCheck 7 2688 = true := by decide +kernel

theorem checked_2816 : allBlock stepCheck 7 2816 = true := by decide +kernel

theorem checked_2944 : allBlock stepCheck 7 2944 = true := by decide +kernel

theorem checked_3072 : allBlock stepCheck 7 3072 = true := by decide +kernel

theorem checked_3200 : allBlock stepCheck 7 3200 = true := by decide +kernel

theorem checked_3328 : allBlock stepCheck 7 3328 = true := by decide +kernel

theorem checked_3456 : allBlock stepCheck 7 3456 = true := by decide +kernel

theorem checked_3584 : allBlock stepCheck 7 3584 = true := by decide +kernel

theorem checked_3712 : allBlock stepCheck 7 3712 = true := by decide +kernel

theorem checked_3840 : allBlock stepCheck 7 3840 = true := by decide +kernel

theorem checked_3968 : allBlock stepCheck 7 3968 = true := by decide +kernel

theorem checked_4096 : allBlock stepCheck 7 4096 = true := by decide +kernel

theorem checked_4224 : allBlock stepCheck 7 4224 = true := by decide +kernel

theorem checked_4352 : allBlock stepCheck 7 4352 = true := by decide +kernel

theorem checked_4480 : allBlock stepCheck 2 4480 = true := by decide +kernel

theorem checked_4484 : allBlock stepCheck 0 4484 = true := by decide +kernel

theorem all_hold : ∀ n, n < 4485 →
    Holds threeSubgroup localGenerator (definitions.repr localGenerator) (facts n) := by
  have h128 := block_sound 7 0 (fun n hn => (Nat.not_lt_zero n hn).elim) checked_0
  have h256 := block_sound 7 128 h128 checked_128
  have h384 := block_sound 7 256 h256 checked_256
  have h512 := block_sound 7 384 h384 checked_384
  have h640 := block_sound 7 512 h512 checked_512
  have h768 := block_sound 7 640 h640 checked_640
  have h896 := block_sound 7 768 h768 checked_768
  have h1024 := block_sound 7 896 h896 checked_896
  have h1152 := block_sound 7 1024 h1024 checked_1024
  have h1280 := block_sound 7 1152 h1152 checked_1152
  have h1408 := block_sound 7 1280 h1280 checked_1280
  have h1536 := block_sound 7 1408 h1408 checked_1408
  have h1664 := block_sound 7 1536 h1536 checked_1536
  have h1792 := block_sound 7 1664 h1664 checked_1664
  have h1920 := block_sound 7 1792 h1792 checked_1792
  have h2048 := block_sound 7 1920 h1920 checked_1920
  have h2176 := block_sound 7 2048 h2048 checked_2048
  have h2304 := block_sound 7 2176 h2176 checked_2176
  have h2432 := block_sound 7 2304 h2304 checked_2304
  have h2560 := block_sound 7 2432 h2432 checked_2432
  have h2688 := block_sound 7 2560 h2560 checked_2560
  have h2816 := block_sound 7 2688 h2688 checked_2688
  have h2944 := block_sound 7 2816 h2816 checked_2816
  have h3072 := block_sound 7 2944 h2944 checked_2944
  have h3200 := block_sound 7 3072 h3072 checked_3072
  have h3328 := block_sound 7 3200 h3200 checked_3200
  have h3456 := block_sound 7 3328 h3328 checked_3328
  have h3584 := block_sound 7 3456 h3456 checked_3456
  have h3712 := block_sound 7 3584 h3584 checked_3584
  have h3840 := block_sound 7 3712 h3712 checked_3712
  have h3968 := block_sound 7 3840 h3840 checked_3840
  have h4096 := block_sound 7 3968 h3968 checked_3968
  have h4224 := block_sound 7 4096 h4096 checked_4096
  have h4352 := block_sound 7 4224 h4224 checked_4224
  have h4480 := block_sound 7 4352 h4352 checked_4352
  have h4484 := block_sound 2 4480 h4480 checked_4480
  have h4485 := block_sound 0 4484 h4484 checked_4484
  exact h4485

def output (n : Nat) : Nat := min (outputCode n) 4484

def shapeAt (n : Nat) : Bool :=
  if n < 202 then factBEq (facts (output n)) ⟨0, [decode n], 0⟩ else true

theorem shapes_checked : allBlock shapeAt 8 0 = true := by decide +kernel

theorem shape (n : Nat) (hn : n < 202) : facts (output n) = ⟨0, [decode n], 0⟩ := by
  have h := allBlock_spec shapeAt 8 0 shapes_checked n (Nat.zero_le _) (by omega)
  simp only [shapeAt, if_pos hn] at h
  exact (factBEq_eq_true_iff _ _).mp h

theorem output_lt (n : Nat) : output n < 4485 :=
  Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)

end GenerationCertificate

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier
