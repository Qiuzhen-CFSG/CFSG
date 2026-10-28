module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_50176 : checkChunk representatives relations facts operations 50176 128 = true := by decide +kernel

theorem checked_50304 : checkChunk representatives relations facts operations 50304 128 = true := by decide +kernel

theorem checked_50432 : checkChunk representatives relations facts operations 50432 128 = true := by decide +kernel

theorem checked_50560 : checkChunk representatives relations facts operations 50560 128 = true := by decide +kernel

theorem checked_50688 : checkChunk representatives relations facts operations 50688 128 = true := by decide +kernel

theorem checked_50816 : checkChunk representatives relations facts operations 50816 128 = true := by decide +kernel

theorem checked_50944 : checkChunk representatives relations facts operations 50944 128 = true := by decide +kernel

theorem checked_51072 : checkChunk representatives relations facts operations 51072 128 = true := by decide +kernel

theorem holds_block_50176 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 50176 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 51200 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h50176 := chunk_sound x representatives relations hr representatives_zero facts operations 50176 128 prior checked_50176

  have h50304 := chunk_sound x representatives relations hr representatives_zero facts operations 50304 128 h50176 checked_50304

  have h50432 := chunk_sound x representatives relations hr representatives_zero facts operations 50432 128 h50304 checked_50432

  have h50560 := chunk_sound x representatives relations hr representatives_zero facts operations 50560 128 h50432 checked_50560

  have h50688 := chunk_sound x representatives relations hr representatives_zero facts operations 50688 128 h50560 checked_50688

  have h50816 := chunk_sound x representatives relations hr representatives_zero facts operations 50816 128 h50688 checked_50816

  have h50944 := chunk_sound x representatives relations hr representatives_zero facts operations 50944 128 h50816 checked_50944

  have h51072 := chunk_sound x representatives relations hr representatives_zero facts operations 51072 128 h50944 checked_51072

  exact h51072

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
