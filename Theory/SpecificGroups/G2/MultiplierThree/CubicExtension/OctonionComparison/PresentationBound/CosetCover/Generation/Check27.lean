module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_27648 : checkChunk representatives relations facts operations 27648 128 = true := by decide +kernel

theorem checked_27776 : checkChunk representatives relations facts operations 27776 128 = true := by decide +kernel

theorem checked_27904 : checkChunk representatives relations facts operations 27904 128 = true := by decide +kernel

theorem checked_28032 : checkChunk representatives relations facts operations 28032 128 = true := by decide +kernel

theorem checked_28160 : checkChunk representatives relations facts operations 28160 128 = true := by decide +kernel

theorem checked_28288 : checkChunk representatives relations facts operations 28288 128 = true := by decide +kernel

theorem checked_28416 : checkChunk representatives relations facts operations 28416 128 = true := by decide +kernel

theorem checked_28544 : checkChunk representatives relations facts operations 28544 128 = true := by decide +kernel

theorem holds_block_27648 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 27648 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 28672 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h27648 := chunk_sound x representatives relations hr representatives_zero facts operations 27648 128 prior checked_27648

  have h27776 := chunk_sound x representatives relations hr representatives_zero facts operations 27776 128 h27648 checked_27776

  have h27904 := chunk_sound x representatives relations hr representatives_zero facts operations 27904 128 h27776 checked_27904

  have h28032 := chunk_sound x representatives relations hr representatives_zero facts operations 28032 128 h27904 checked_28032

  have h28160 := chunk_sound x representatives relations hr representatives_zero facts operations 28160 128 h28032 checked_28160

  have h28288 := chunk_sound x representatives relations hr representatives_zero facts operations 28288 128 h28160 checked_28288

  have h28416 := chunk_sound x representatives relations hr representatives_zero facts operations 28416 128 h28288 checked_28416

  have h28544 := chunk_sound x representatives relations hr representatives_zero facts operations 28544 128 h28416 checked_28544

  exact h28544

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
