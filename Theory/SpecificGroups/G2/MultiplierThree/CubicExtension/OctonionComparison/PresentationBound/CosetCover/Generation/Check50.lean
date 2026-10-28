module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_51200 : checkChunk representatives relations facts operations 51200 128 = true := by decide +kernel

theorem checked_51328 : checkChunk representatives relations facts operations 51328 128 = true := by decide +kernel

theorem checked_51456 : checkChunk representatives relations facts operations 51456 128 = true := by decide +kernel

theorem checked_51584 : checkChunk representatives relations facts operations 51584 128 = true := by decide +kernel

theorem checked_51712 : checkChunk representatives relations facts operations 51712 128 = true := by decide +kernel

theorem checked_51840 : checkChunk representatives relations facts operations 51840 128 = true := by decide +kernel

theorem checked_51968 : checkChunk representatives relations facts operations 51968 128 = true := by decide +kernel

theorem checked_52096 : checkChunk representatives relations facts operations 52096 128 = true := by decide +kernel

theorem holds_block_51200 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 51200 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 52224 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h51200 := chunk_sound x representatives relations hr representatives_zero facts operations 51200 128 prior checked_51200

  have h51328 := chunk_sound x representatives relations hr representatives_zero facts operations 51328 128 h51200 checked_51328

  have h51456 := chunk_sound x representatives relations hr representatives_zero facts operations 51456 128 h51328 checked_51456

  have h51584 := chunk_sound x representatives relations hr representatives_zero facts operations 51584 128 h51456 checked_51584

  have h51712 := chunk_sound x representatives relations hr representatives_zero facts operations 51712 128 h51584 checked_51712

  have h51840 := chunk_sound x representatives relations hr representatives_zero facts operations 51840 128 h51712 checked_51840

  have h51968 := chunk_sound x representatives relations hr representatives_zero facts operations 51968 128 h51840 checked_51968

  have h52096 := chunk_sound x representatives relations hr representatives_zero facts operations 52096 128 h51968 checked_52096

  exact h52096

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
