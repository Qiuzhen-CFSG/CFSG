module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_17408 : checkChunk representatives relations facts operations 17408 128 = true := by decide +kernel

theorem checked_17536 : checkChunk representatives relations facts operations 17536 128 = true := by decide +kernel

theorem checked_17664 : checkChunk representatives relations facts operations 17664 128 = true := by decide +kernel

theorem checked_17792 : checkChunk representatives relations facts operations 17792 128 = true := by decide +kernel

theorem checked_17920 : checkChunk representatives relations facts operations 17920 128 = true := by decide +kernel

theorem checked_18048 : checkChunk representatives relations facts operations 18048 128 = true := by decide +kernel

theorem checked_18176 : checkChunk representatives relations facts operations 18176 128 = true := by decide +kernel

theorem checked_18304 : checkChunk representatives relations facts operations 18304 128 = true := by decide +kernel

theorem holds_block_17408 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 17408 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 18432 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h17408 := chunk_sound x representatives relations hr representatives_zero facts operations 17408 128 prior checked_17408

  have h17536 := chunk_sound x representatives relations hr representatives_zero facts operations 17536 128 h17408 checked_17536

  have h17664 := chunk_sound x representatives relations hr representatives_zero facts operations 17664 128 h17536 checked_17664

  have h17792 := chunk_sound x representatives relations hr representatives_zero facts operations 17792 128 h17664 checked_17792

  have h17920 := chunk_sound x representatives relations hr representatives_zero facts operations 17920 128 h17792 checked_17920

  have h18048 := chunk_sound x representatives relations hr representatives_zero facts operations 18048 128 h17920 checked_18048

  have h18176 := chunk_sound x representatives relations hr representatives_zero facts operations 18176 128 h18048 checked_18176

  have h18304 := chunk_sound x representatives relations hr representatives_zero facts operations 18304 128 h18176 checked_18304

  exact h18304

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
