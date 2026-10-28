module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_2048 : checkChunk representatives relations facts operations 2048 128 = true := by decide +kernel

theorem checked_2176 : checkChunk representatives relations facts operations 2176 128 = true := by decide +kernel

theorem checked_2304 : checkChunk representatives relations facts operations 2304 128 = true := by decide +kernel

theorem checked_2432 : checkChunk representatives relations facts operations 2432 128 = true := by decide +kernel

theorem checked_2560 : checkChunk representatives relations facts operations 2560 128 = true := by decide +kernel

theorem checked_2688 : checkChunk representatives relations facts operations 2688 128 = true := by decide +kernel

theorem checked_2816 : checkChunk representatives relations facts operations 2816 128 = true := by decide +kernel

theorem checked_2944 : checkChunk representatives relations facts operations 2944 128 = true := by decide +kernel

theorem holds_block_2048 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 2048 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 3072 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h2048 := chunk_sound x representatives relations hr representatives_zero facts operations 2048 128 prior checked_2048

  have h2176 := chunk_sound x representatives relations hr representatives_zero facts operations 2176 128 h2048 checked_2176

  have h2304 := chunk_sound x representatives relations hr representatives_zero facts operations 2304 128 h2176 checked_2304

  have h2432 := chunk_sound x representatives relations hr representatives_zero facts operations 2432 128 h2304 checked_2432

  have h2560 := chunk_sound x representatives relations hr representatives_zero facts operations 2560 128 h2432 checked_2560

  have h2688 := chunk_sound x representatives relations hr representatives_zero facts operations 2688 128 h2560 checked_2688

  have h2816 := chunk_sound x representatives relations hr representatives_zero facts operations 2816 128 h2688 checked_2816

  have h2944 := chunk_sound x representatives relations hr representatives_zero facts operations 2944 128 h2816 checked_2944

  exact h2944

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
