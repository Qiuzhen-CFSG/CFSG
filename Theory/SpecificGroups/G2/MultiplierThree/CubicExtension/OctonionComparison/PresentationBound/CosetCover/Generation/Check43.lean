module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_44032 : checkChunk representatives relations facts operations 44032 128 = true := by decide +kernel

theorem checked_44160 : checkChunk representatives relations facts operations 44160 128 = true := by decide +kernel

theorem checked_44288 : checkChunk representatives relations facts operations 44288 128 = true := by decide +kernel

theorem checked_44416 : checkChunk representatives relations facts operations 44416 128 = true := by decide +kernel

theorem checked_44544 : checkChunk representatives relations facts operations 44544 128 = true := by decide +kernel

theorem checked_44672 : checkChunk representatives relations facts operations 44672 128 = true := by decide +kernel

theorem checked_44800 : checkChunk representatives relations facts operations 44800 128 = true := by decide +kernel

theorem checked_44928 : checkChunk representatives relations facts operations 44928 128 = true := by decide +kernel

theorem holds_block_44032 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 44032 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 45056 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h44032 := chunk_sound x representatives relations hr representatives_zero facts operations 44032 128 prior checked_44032

  have h44160 := chunk_sound x representatives relations hr representatives_zero facts operations 44160 128 h44032 checked_44160

  have h44288 := chunk_sound x representatives relations hr representatives_zero facts operations 44288 128 h44160 checked_44288

  have h44416 := chunk_sound x representatives relations hr representatives_zero facts operations 44416 128 h44288 checked_44416

  have h44544 := chunk_sound x representatives relations hr representatives_zero facts operations 44544 128 h44416 checked_44544

  have h44672 := chunk_sound x representatives relations hr representatives_zero facts operations 44672 128 h44544 checked_44672

  have h44800 := chunk_sound x representatives relations hr representatives_zero facts operations 44800 128 h44672 checked_44800

  have h44928 := chunk_sound x representatives relations hr representatives_zero facts operations 44928 128 h44800 checked_44928

  exact h44928

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
