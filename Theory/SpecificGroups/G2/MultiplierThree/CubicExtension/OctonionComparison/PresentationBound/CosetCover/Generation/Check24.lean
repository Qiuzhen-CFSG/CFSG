module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_24576 : checkChunk representatives relations facts operations 24576 128 = true := by decide +kernel

theorem checked_24704 : checkChunk representatives relations facts operations 24704 128 = true := by decide +kernel

theorem checked_24832 : checkChunk representatives relations facts operations 24832 128 = true := by decide +kernel

theorem checked_24960 : checkChunk representatives relations facts operations 24960 128 = true := by decide +kernel

theorem checked_25088 : checkChunk representatives relations facts operations 25088 128 = true := by decide +kernel

theorem checked_25216 : checkChunk representatives relations facts operations 25216 128 = true := by decide +kernel

theorem checked_25344 : checkChunk representatives relations facts operations 25344 128 = true := by decide +kernel

theorem checked_25472 : checkChunk representatives relations facts operations 25472 128 = true := by decide +kernel

theorem holds_block_24576 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 24576 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 25600 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h24576 := chunk_sound x representatives relations hr representatives_zero facts operations 24576 128 prior checked_24576

  have h24704 := chunk_sound x representatives relations hr representatives_zero facts operations 24704 128 h24576 checked_24704

  have h24832 := chunk_sound x representatives relations hr representatives_zero facts operations 24832 128 h24704 checked_24832

  have h24960 := chunk_sound x representatives relations hr representatives_zero facts operations 24960 128 h24832 checked_24960

  have h25088 := chunk_sound x representatives relations hr representatives_zero facts operations 25088 128 h24960 checked_25088

  have h25216 := chunk_sound x representatives relations hr representatives_zero facts operations 25216 128 h25088 checked_25216

  have h25344 := chunk_sound x representatives relations hr representatives_zero facts operations 25344 128 h25216 checked_25344

  have h25472 := chunk_sound x representatives relations hr representatives_zero facts operations 25472 128 h25344 checked_25472

  exact h25472

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
