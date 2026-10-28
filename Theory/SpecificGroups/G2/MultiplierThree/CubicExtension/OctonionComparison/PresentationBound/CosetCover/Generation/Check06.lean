module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_6144 : checkChunk representatives relations facts operations 6144 128 = true := by decide +kernel

theorem checked_6272 : checkChunk representatives relations facts operations 6272 128 = true := by decide +kernel

theorem checked_6400 : checkChunk representatives relations facts operations 6400 128 = true := by decide +kernel

theorem checked_6528 : checkChunk representatives relations facts operations 6528 128 = true := by decide +kernel

theorem checked_6656 : checkChunk representatives relations facts operations 6656 128 = true := by decide +kernel

theorem checked_6784 : checkChunk representatives relations facts operations 6784 128 = true := by decide +kernel

theorem checked_6912 : checkChunk representatives relations facts operations 6912 128 = true := by decide +kernel

theorem checked_7040 : checkChunk representatives relations facts operations 7040 128 = true := by decide +kernel

theorem holds_block_6144 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 6144 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 7168 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h6144 := chunk_sound x representatives relations hr representatives_zero facts operations 6144 128 prior checked_6144

  have h6272 := chunk_sound x representatives relations hr representatives_zero facts operations 6272 128 h6144 checked_6272

  have h6400 := chunk_sound x representatives relations hr representatives_zero facts operations 6400 128 h6272 checked_6400

  have h6528 := chunk_sound x representatives relations hr representatives_zero facts operations 6528 128 h6400 checked_6528

  have h6656 := chunk_sound x representatives relations hr representatives_zero facts operations 6656 128 h6528 checked_6656

  have h6784 := chunk_sound x representatives relations hr representatives_zero facts operations 6784 128 h6656 checked_6784

  have h6912 := chunk_sound x representatives relations hr representatives_zero facts operations 6912 128 h6784 checked_6912

  have h7040 := chunk_sound x representatives relations hr representatives_zero facts operations 7040 128 h6912 checked_7040

  exact h7040

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
