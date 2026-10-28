module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_25600 : checkChunk representatives relations facts operations 25600 128 = true := by decide +kernel

theorem checked_25728 : checkChunk representatives relations facts operations 25728 128 = true := by decide +kernel

theorem checked_25856 : checkChunk representatives relations facts operations 25856 128 = true := by decide +kernel

theorem checked_25984 : checkChunk representatives relations facts operations 25984 128 = true := by decide +kernel

theorem checked_26112 : checkChunk representatives relations facts operations 26112 128 = true := by decide +kernel

theorem checked_26240 : checkChunk representatives relations facts operations 26240 128 = true := by decide +kernel

theorem checked_26368 : checkChunk representatives relations facts operations 26368 128 = true := by decide +kernel

theorem checked_26496 : checkChunk representatives relations facts operations 26496 128 = true := by decide +kernel

theorem holds_block_25600 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 25600 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 26624 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h25600 := chunk_sound x representatives relations hr representatives_zero facts operations 25600 128 prior checked_25600

  have h25728 := chunk_sound x representatives relations hr representatives_zero facts operations 25728 128 h25600 checked_25728

  have h25856 := chunk_sound x representatives relations hr representatives_zero facts operations 25856 128 h25728 checked_25856

  have h25984 := chunk_sound x representatives relations hr representatives_zero facts operations 25984 128 h25856 checked_25984

  have h26112 := chunk_sound x representatives relations hr representatives_zero facts operations 26112 128 h25984 checked_26112

  have h26240 := chunk_sound x representatives relations hr representatives_zero facts operations 26240 128 h26112 checked_26240

  have h26368 := chunk_sound x representatives relations hr representatives_zero facts operations 26368 128 h26240 checked_26368

  have h26496 := chunk_sound x representatives relations hr representatives_zero facts operations 26496 128 h26368 checked_26496

  exact h26496

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
