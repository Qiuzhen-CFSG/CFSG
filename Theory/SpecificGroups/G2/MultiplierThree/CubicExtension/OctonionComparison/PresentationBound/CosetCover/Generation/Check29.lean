module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_29696 : checkChunk representatives relations facts operations 29696 128 = true := by decide +kernel

theorem checked_29824 : checkChunk representatives relations facts operations 29824 128 = true := by decide +kernel

theorem checked_29952 : checkChunk representatives relations facts operations 29952 128 = true := by decide +kernel

theorem checked_30080 : checkChunk representatives relations facts operations 30080 128 = true := by decide +kernel

theorem checked_30208 : checkChunk representatives relations facts operations 30208 128 = true := by decide +kernel

theorem checked_30336 : checkChunk representatives relations facts operations 30336 128 = true := by decide +kernel

theorem checked_30464 : checkChunk representatives relations facts operations 30464 128 = true := by decide +kernel

theorem checked_30592 : checkChunk representatives relations facts operations 30592 128 = true := by decide +kernel

theorem holds_block_29696 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 29696 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 30720 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h29696 := chunk_sound x representatives relations hr representatives_zero facts operations 29696 128 prior checked_29696

  have h29824 := chunk_sound x representatives relations hr representatives_zero facts operations 29824 128 h29696 checked_29824

  have h29952 := chunk_sound x representatives relations hr representatives_zero facts operations 29952 128 h29824 checked_29952

  have h30080 := chunk_sound x representatives relations hr representatives_zero facts operations 30080 128 h29952 checked_30080

  have h30208 := chunk_sound x representatives relations hr representatives_zero facts operations 30208 128 h30080 checked_30208

  have h30336 := chunk_sound x representatives relations hr representatives_zero facts operations 30336 128 h30208 checked_30336

  have h30464 := chunk_sound x representatives relations hr representatives_zero facts operations 30464 128 h30336 checked_30464

  have h30592 := chunk_sound x representatives relations hr representatives_zero facts operations 30592 128 h30464 checked_30592

  exact h30592

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
