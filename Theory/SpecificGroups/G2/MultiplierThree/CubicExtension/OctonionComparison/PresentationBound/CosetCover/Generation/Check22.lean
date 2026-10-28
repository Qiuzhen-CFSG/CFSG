module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_22528 : checkChunk representatives relations facts operations 22528 128 = true := by decide +kernel

theorem checked_22656 : checkChunk representatives relations facts operations 22656 128 = true := by decide +kernel

theorem checked_22784 : checkChunk representatives relations facts operations 22784 128 = true := by decide +kernel

theorem checked_22912 : checkChunk representatives relations facts operations 22912 128 = true := by decide +kernel

theorem checked_23040 : checkChunk representatives relations facts operations 23040 128 = true := by decide +kernel

theorem checked_23168 : checkChunk representatives relations facts operations 23168 128 = true := by decide +kernel

theorem checked_23296 : checkChunk representatives relations facts operations 23296 128 = true := by decide +kernel

theorem checked_23424 : checkChunk representatives relations facts operations 23424 128 = true := by decide +kernel

theorem holds_block_22528 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 22528 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 23552 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h22528 := chunk_sound x representatives relations hr representatives_zero facts operations 22528 128 prior checked_22528

  have h22656 := chunk_sound x representatives relations hr representatives_zero facts operations 22656 128 h22528 checked_22656

  have h22784 := chunk_sound x representatives relations hr representatives_zero facts operations 22784 128 h22656 checked_22784

  have h22912 := chunk_sound x representatives relations hr representatives_zero facts operations 22912 128 h22784 checked_22912

  have h23040 := chunk_sound x representatives relations hr representatives_zero facts operations 23040 128 h22912 checked_23040

  have h23168 := chunk_sound x representatives relations hr representatives_zero facts operations 23168 128 h23040 checked_23168

  have h23296 := chunk_sound x representatives relations hr representatives_zero facts operations 23296 128 h23168 checked_23296

  have h23424 := chunk_sound x representatives relations hr representatives_zero facts operations 23424 128 h23296 checked_23424

  exact h23424

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
