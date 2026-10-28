module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_54272 : checkChunk representatives relations facts operations 54272 128 = true := by decide +kernel

theorem checked_54400 : checkChunk representatives relations facts operations 54400 128 = true := by decide +kernel

theorem checked_54528 : checkChunk representatives relations facts operations 54528 128 = true := by decide +kernel

theorem checked_54656 : checkChunk representatives relations facts operations 54656 128 = true := by decide +kernel

theorem checked_54784 : checkChunk representatives relations facts operations 54784 128 = true := by decide +kernel

theorem checked_54912 : checkChunk representatives relations facts operations 54912 128 = true := by decide +kernel

theorem checked_55040 : checkChunk representatives relations facts operations 55040 128 = true := by decide +kernel

theorem checked_55168 : checkChunk representatives relations facts operations 55168 128 = true := by decide +kernel

theorem holds_block_54272 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 54272 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 55296 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h54272 := chunk_sound x representatives relations hr representatives_zero facts operations 54272 128 prior checked_54272

  have h54400 := chunk_sound x representatives relations hr representatives_zero facts operations 54400 128 h54272 checked_54400

  have h54528 := chunk_sound x representatives relations hr representatives_zero facts operations 54528 128 h54400 checked_54528

  have h54656 := chunk_sound x representatives relations hr representatives_zero facts operations 54656 128 h54528 checked_54656

  have h54784 := chunk_sound x representatives relations hr representatives_zero facts operations 54784 128 h54656 checked_54784

  have h54912 := chunk_sound x representatives relations hr representatives_zero facts operations 54912 128 h54784 checked_54912

  have h55040 := chunk_sound x representatives relations hr representatives_zero facts operations 55040 128 h54912 checked_55040

  have h55168 := chunk_sound x representatives relations hr representatives_zero facts operations 55168 128 h55040 checked_55168

  exact h55168

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
