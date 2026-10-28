module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_62464 : checkChunk representatives relations facts operations 62464 128 = true := by decide +kernel

theorem checked_62592 : checkChunk representatives relations facts operations 62592 128 = true := by decide +kernel

theorem checked_62720 : checkChunk representatives relations facts operations 62720 128 = true := by decide +kernel

theorem checked_62848 : checkChunk representatives relations facts operations 62848 128 = true := by decide +kernel

theorem checked_62976 : checkChunk representatives relations facts operations 62976 128 = true := by decide +kernel

theorem checked_63104 : checkChunk representatives relations facts operations 63104 128 = true := by decide +kernel

theorem checked_63232 : checkChunk representatives relations facts operations 63232 128 = true := by decide +kernel

theorem checked_63360 : checkChunk representatives relations facts operations 63360 128 = true := by decide +kernel

theorem holds_block_62464 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 62464 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 63488 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h62464 := chunk_sound x representatives relations hr representatives_zero facts operations 62464 128 prior checked_62464

  have h62592 := chunk_sound x representatives relations hr representatives_zero facts operations 62592 128 h62464 checked_62592

  have h62720 := chunk_sound x representatives relations hr representatives_zero facts operations 62720 128 h62592 checked_62720

  have h62848 := chunk_sound x representatives relations hr representatives_zero facts operations 62848 128 h62720 checked_62848

  have h62976 := chunk_sound x representatives relations hr representatives_zero facts operations 62976 128 h62848 checked_62976

  have h63104 := chunk_sound x representatives relations hr representatives_zero facts operations 63104 128 h62976 checked_63104

  have h63232 := chunk_sound x representatives relations hr representatives_zero facts operations 63232 128 h63104 checked_63232

  have h63360 := chunk_sound x representatives relations hr representatives_zero facts operations 63360 128 h63232 checked_63360

  exact h63360

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
