module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_70656 : checkChunk representatives relations facts operations 70656 128 = true := by decide +kernel

theorem checked_70784 : checkChunk representatives relations facts operations 70784 128 = true := by decide +kernel

theorem checked_70912 : checkChunk representatives relations facts operations 70912 128 = true := by decide +kernel

theorem checked_71040 : checkChunk representatives relations facts operations 71040 128 = true := by decide +kernel

theorem checked_71168 : checkChunk representatives relations facts operations 71168 128 = true := by decide +kernel

theorem checked_71296 : checkChunk representatives relations facts operations 71296 128 = true := by decide +kernel

theorem checked_71424 : checkChunk representatives relations facts operations 71424 128 = true := by decide +kernel

theorem checked_71552 : checkChunk representatives relations facts operations 71552 128 = true := by decide +kernel

theorem holds_block_70656 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 70656 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 71680 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h70656 := chunk_sound x representatives relations hr representatives_zero facts operations 70656 128 prior checked_70656

  have h70784 := chunk_sound x representatives relations hr representatives_zero facts operations 70784 128 h70656 checked_70784

  have h70912 := chunk_sound x representatives relations hr representatives_zero facts operations 70912 128 h70784 checked_70912

  have h71040 := chunk_sound x representatives relations hr representatives_zero facts operations 71040 128 h70912 checked_71040

  have h71168 := chunk_sound x representatives relations hr representatives_zero facts operations 71168 128 h71040 checked_71168

  have h71296 := chunk_sound x representatives relations hr representatives_zero facts operations 71296 128 h71168 checked_71296

  have h71424 := chunk_sound x representatives relations hr representatives_zero facts operations 71424 128 h71296 checked_71424

  have h71552 := chunk_sound x representatives relations hr representatives_zero facts operations 71552 128 h71424 checked_71552

  exact h71552

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
