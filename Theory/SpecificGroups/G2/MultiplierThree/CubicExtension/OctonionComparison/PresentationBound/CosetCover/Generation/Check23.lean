module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_23552 : checkChunk representatives relations facts operations 23552 128 = true := by decide +kernel

theorem checked_23680 : checkChunk representatives relations facts operations 23680 128 = true := by decide +kernel

theorem checked_23808 : checkChunk representatives relations facts operations 23808 128 = true := by decide +kernel

theorem checked_23936 : checkChunk representatives relations facts operations 23936 128 = true := by decide +kernel

theorem checked_24064 : checkChunk representatives relations facts operations 24064 128 = true := by decide +kernel

theorem checked_24192 : checkChunk representatives relations facts operations 24192 128 = true := by decide +kernel

theorem checked_24320 : checkChunk representatives relations facts operations 24320 128 = true := by decide +kernel

theorem checked_24448 : checkChunk representatives relations facts operations 24448 128 = true := by decide +kernel

theorem holds_block_23552 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 23552 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 24576 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h23552 := chunk_sound x representatives relations hr representatives_zero facts operations 23552 128 prior checked_23552

  have h23680 := chunk_sound x representatives relations hr representatives_zero facts operations 23680 128 h23552 checked_23680

  have h23808 := chunk_sound x representatives relations hr representatives_zero facts operations 23808 128 h23680 checked_23808

  have h23936 := chunk_sound x representatives relations hr representatives_zero facts operations 23936 128 h23808 checked_23936

  have h24064 := chunk_sound x representatives relations hr representatives_zero facts operations 24064 128 h23936 checked_24064

  have h24192 := chunk_sound x representatives relations hr representatives_zero facts operations 24192 128 h24064 checked_24192

  have h24320 := chunk_sound x representatives relations hr representatives_zero facts operations 24320 128 h24192 checked_24320

  have h24448 := chunk_sound x representatives relations hr representatives_zero facts operations 24448 128 h24320 checked_24448

  exact h24448

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
