module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_59392 : checkChunk representatives relations facts operations 59392 128 = true := by decide +kernel

theorem checked_59520 : checkChunk representatives relations facts operations 59520 128 = true := by decide +kernel

theorem checked_59648 : checkChunk representatives relations facts operations 59648 128 = true := by decide +kernel

theorem checked_59776 : checkChunk representatives relations facts operations 59776 128 = true := by decide +kernel

theorem checked_59904 : checkChunk representatives relations facts operations 59904 128 = true := by decide +kernel

theorem checked_60032 : checkChunk representatives relations facts operations 60032 128 = true := by decide +kernel

theorem checked_60160 : checkChunk representatives relations facts operations 60160 128 = true := by decide +kernel

theorem checked_60288 : checkChunk representatives relations facts operations 60288 128 = true := by decide +kernel

theorem holds_block_59392 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 59392 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 60416 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h59392 := chunk_sound x representatives relations hr representatives_zero facts operations 59392 128 prior checked_59392

  have h59520 := chunk_sound x representatives relations hr representatives_zero facts operations 59520 128 h59392 checked_59520

  have h59648 := chunk_sound x representatives relations hr representatives_zero facts operations 59648 128 h59520 checked_59648

  have h59776 := chunk_sound x representatives relations hr representatives_zero facts operations 59776 128 h59648 checked_59776

  have h59904 := chunk_sound x representatives relations hr representatives_zero facts operations 59904 128 h59776 checked_59904

  have h60032 := chunk_sound x representatives relations hr representatives_zero facts operations 60032 128 h59904 checked_60032

  have h60160 := chunk_sound x representatives relations hr representatives_zero facts operations 60160 128 h60032 checked_60160

  have h60288 := chunk_sound x representatives relations hr representatives_zero facts operations 60288 128 h60160 checked_60288

  exact h60288

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
