module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_7168 : checkChunk representatives relations facts operations 7168 128 = true := by decide +kernel

theorem checked_7296 : checkChunk representatives relations facts operations 7296 128 = true := by decide +kernel

theorem checked_7424 : checkChunk representatives relations facts operations 7424 128 = true := by decide +kernel

theorem checked_7552 : checkChunk representatives relations facts operations 7552 128 = true := by decide +kernel

theorem checked_7680 : checkChunk representatives relations facts operations 7680 128 = true := by decide +kernel

theorem checked_7808 : checkChunk representatives relations facts operations 7808 128 = true := by decide +kernel

theorem checked_7936 : checkChunk representatives relations facts operations 7936 128 = true := by decide +kernel

theorem checked_8064 : checkChunk representatives relations facts operations 8064 128 = true := by decide +kernel

theorem holds_block_7168 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 7168 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 8192 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h7168 := chunk_sound x representatives relations hr representatives_zero facts operations 7168 128 prior checked_7168

  have h7296 := chunk_sound x representatives relations hr representatives_zero facts operations 7296 128 h7168 checked_7296

  have h7424 := chunk_sound x representatives relations hr representatives_zero facts operations 7424 128 h7296 checked_7424

  have h7552 := chunk_sound x representatives relations hr representatives_zero facts operations 7552 128 h7424 checked_7552

  have h7680 := chunk_sound x representatives relations hr representatives_zero facts operations 7680 128 h7552 checked_7680

  have h7808 := chunk_sound x representatives relations hr representatives_zero facts operations 7808 128 h7680 checked_7808

  have h7936 := chunk_sound x representatives relations hr representatives_zero facts operations 7936 128 h7808 checked_7936

  have h8064 := chunk_sound x representatives relations hr representatives_zero facts operations 8064 128 h7936 checked_8064

  exact h8064

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
