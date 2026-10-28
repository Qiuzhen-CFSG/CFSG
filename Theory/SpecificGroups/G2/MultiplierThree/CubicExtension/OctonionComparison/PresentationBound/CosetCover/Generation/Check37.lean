module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_37888 : checkChunk representatives relations facts operations 37888 128 = true := by decide +kernel

theorem checked_38016 : checkChunk representatives relations facts operations 38016 128 = true := by decide +kernel

theorem checked_38144 : checkChunk representatives relations facts operations 38144 128 = true := by decide +kernel

theorem checked_38272 : checkChunk representatives relations facts operations 38272 128 = true := by decide +kernel

theorem checked_38400 : checkChunk representatives relations facts operations 38400 128 = true := by decide +kernel

theorem checked_38528 : checkChunk representatives relations facts operations 38528 128 = true := by decide +kernel

theorem checked_38656 : checkChunk representatives relations facts operations 38656 128 = true := by decide +kernel

theorem checked_38784 : checkChunk representatives relations facts operations 38784 128 = true := by decide +kernel

theorem holds_block_37888 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 37888 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 38912 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h37888 := chunk_sound x representatives relations hr representatives_zero facts operations 37888 128 prior checked_37888

  have h38016 := chunk_sound x representatives relations hr representatives_zero facts operations 38016 128 h37888 checked_38016

  have h38144 := chunk_sound x representatives relations hr representatives_zero facts operations 38144 128 h38016 checked_38144

  have h38272 := chunk_sound x representatives relations hr representatives_zero facts operations 38272 128 h38144 checked_38272

  have h38400 := chunk_sound x representatives relations hr representatives_zero facts operations 38400 128 h38272 checked_38400

  have h38528 := chunk_sound x representatives relations hr representatives_zero facts operations 38528 128 h38400 checked_38528

  have h38656 := chunk_sound x representatives relations hr representatives_zero facts operations 38656 128 h38528 checked_38656

  have h38784 := chunk_sound x representatives relations hr representatives_zero facts operations 38784 128 h38656 checked_38784

  exact h38784

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
