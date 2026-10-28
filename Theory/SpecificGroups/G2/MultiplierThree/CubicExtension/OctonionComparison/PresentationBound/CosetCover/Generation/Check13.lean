module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_13312 : checkChunk representatives relations facts operations 13312 128 = true := by decide +kernel

theorem checked_13440 : checkChunk representatives relations facts operations 13440 128 = true := by decide +kernel

theorem checked_13568 : checkChunk representatives relations facts operations 13568 128 = true := by decide +kernel

theorem checked_13696 : checkChunk representatives relations facts operations 13696 128 = true := by decide +kernel

theorem checked_13824 : checkChunk representatives relations facts operations 13824 128 = true := by decide +kernel

theorem checked_13952 : checkChunk representatives relations facts operations 13952 128 = true := by decide +kernel

theorem checked_14080 : checkChunk representatives relations facts operations 14080 128 = true := by decide +kernel

theorem checked_14208 : checkChunk representatives relations facts operations 14208 128 = true := by decide +kernel

theorem holds_block_13312 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 13312 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 14336 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h13312 := chunk_sound x representatives relations hr representatives_zero facts operations 13312 128 prior checked_13312

  have h13440 := chunk_sound x representatives relations hr representatives_zero facts operations 13440 128 h13312 checked_13440

  have h13568 := chunk_sound x representatives relations hr representatives_zero facts operations 13568 128 h13440 checked_13568

  have h13696 := chunk_sound x representatives relations hr representatives_zero facts operations 13696 128 h13568 checked_13696

  have h13824 := chunk_sound x representatives relations hr representatives_zero facts operations 13824 128 h13696 checked_13824

  have h13952 := chunk_sound x representatives relations hr representatives_zero facts operations 13952 128 h13824 checked_13952

  have h14080 := chunk_sound x representatives relations hr representatives_zero facts operations 14080 128 h13952 checked_14080

  have h14208 := chunk_sound x representatives relations hr representatives_zero facts operations 14208 128 h14080 checked_14208

  exact h14208

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
