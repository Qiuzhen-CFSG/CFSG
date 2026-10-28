module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_74752 : checkChunk representatives relations facts operations 74752 128 = true := by decide +kernel

theorem checked_74880 : checkChunk representatives relations facts operations 74880 128 = true := by decide +kernel

theorem checked_75008 : checkChunk representatives relations facts operations 75008 128 = true := by decide +kernel

theorem checked_75136 : checkChunk representatives relations facts operations 75136 128 = true := by decide +kernel

theorem checked_75264 : checkChunk representatives relations facts operations 75264 128 = true := by decide +kernel

theorem checked_75392 : checkChunk representatives relations facts operations 75392 128 = true := by decide +kernel

theorem checked_75520 : checkChunk representatives relations facts operations 75520 128 = true := by decide +kernel

theorem checked_75648 : checkChunk representatives relations facts operations 75648 128 = true := by decide +kernel

theorem holds_block_74752 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 74752 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 75776 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h74752 := chunk_sound x representatives relations hr representatives_zero facts operations 74752 128 prior checked_74752

  have h74880 := chunk_sound x representatives relations hr representatives_zero facts operations 74880 128 h74752 checked_74880

  have h75008 := chunk_sound x representatives relations hr representatives_zero facts operations 75008 128 h74880 checked_75008

  have h75136 := chunk_sound x representatives relations hr representatives_zero facts operations 75136 128 h75008 checked_75136

  have h75264 := chunk_sound x representatives relations hr representatives_zero facts operations 75264 128 h75136 checked_75264

  have h75392 := chunk_sound x representatives relations hr representatives_zero facts operations 75392 128 h75264 checked_75392

  have h75520 := chunk_sound x representatives relations hr representatives_zero facts operations 75520 128 h75392 checked_75520

  have h75648 := chunk_sound x representatives relations hr representatives_zero facts operations 75648 128 h75520 checked_75648

  exact h75648

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
