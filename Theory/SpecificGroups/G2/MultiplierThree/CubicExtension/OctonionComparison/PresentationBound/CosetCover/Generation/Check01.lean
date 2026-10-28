module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_1024 : checkChunk representatives relations facts operations 1024 128 = true := by decide +kernel

theorem checked_1152 : checkChunk representatives relations facts operations 1152 128 = true := by decide +kernel

theorem checked_1280 : checkChunk representatives relations facts operations 1280 128 = true := by decide +kernel

theorem checked_1408 : checkChunk representatives relations facts operations 1408 128 = true := by decide +kernel

theorem checked_1536 : checkChunk representatives relations facts operations 1536 128 = true := by decide +kernel

theorem checked_1664 : checkChunk representatives relations facts operations 1664 128 = true := by decide +kernel

theorem checked_1792 : checkChunk representatives relations facts operations 1792 128 = true := by decide +kernel

theorem checked_1920 : checkChunk representatives relations facts operations 1920 128 = true := by decide +kernel

theorem holds_block_1024 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 1024 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 2048 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h1024 := chunk_sound x representatives relations hr representatives_zero facts operations 1024 128 prior checked_1024

  have h1152 := chunk_sound x representatives relations hr representatives_zero facts operations 1152 128 h1024 checked_1152

  have h1280 := chunk_sound x representatives relations hr representatives_zero facts operations 1280 128 h1152 checked_1280

  have h1408 := chunk_sound x representatives relations hr representatives_zero facts operations 1408 128 h1280 checked_1408

  have h1536 := chunk_sound x representatives relations hr representatives_zero facts operations 1536 128 h1408 checked_1536

  have h1664 := chunk_sound x representatives relations hr representatives_zero facts operations 1664 128 h1536 checked_1664

  have h1792 := chunk_sound x representatives relations hr representatives_zero facts operations 1792 128 h1664 checked_1792

  have h1920 := chunk_sound x representatives relations hr representatives_zero facts operations 1920 128 h1792 checked_1920

  exact h1920

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
