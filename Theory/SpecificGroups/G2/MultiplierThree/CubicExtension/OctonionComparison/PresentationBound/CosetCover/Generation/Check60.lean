module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_61440 : checkChunk representatives relations facts operations 61440 128 = true := by decide +kernel

theorem checked_61568 : checkChunk representatives relations facts operations 61568 128 = true := by decide +kernel

theorem checked_61696 : checkChunk representatives relations facts operations 61696 128 = true := by decide +kernel

theorem checked_61824 : checkChunk representatives relations facts operations 61824 128 = true := by decide +kernel

theorem checked_61952 : checkChunk representatives relations facts operations 61952 128 = true := by decide +kernel

theorem checked_62080 : checkChunk representatives relations facts operations 62080 128 = true := by decide +kernel

theorem checked_62208 : checkChunk representatives relations facts operations 62208 128 = true := by decide +kernel

theorem checked_62336 : checkChunk representatives relations facts operations 62336 128 = true := by decide +kernel

theorem holds_block_61440 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 61440 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 62464 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h61440 := chunk_sound x representatives relations hr representatives_zero facts operations 61440 128 prior checked_61440

  have h61568 := chunk_sound x representatives relations hr representatives_zero facts operations 61568 128 h61440 checked_61568

  have h61696 := chunk_sound x representatives relations hr representatives_zero facts operations 61696 128 h61568 checked_61696

  have h61824 := chunk_sound x representatives relations hr representatives_zero facts operations 61824 128 h61696 checked_61824

  have h61952 := chunk_sound x representatives relations hr representatives_zero facts operations 61952 128 h61824 checked_61952

  have h62080 := chunk_sound x representatives relations hr representatives_zero facts operations 62080 128 h61952 checked_62080

  have h62208 := chunk_sound x representatives relations hr representatives_zero facts operations 62208 128 h62080 checked_62208

  have h62336 := chunk_sound x representatives relations hr representatives_zero facts operations 62336 128 h62208 checked_62336

  exact h62336

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
