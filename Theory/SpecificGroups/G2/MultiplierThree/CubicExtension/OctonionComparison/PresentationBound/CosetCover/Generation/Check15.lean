module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_15360 : checkChunk representatives relations facts operations 15360 128 = true := by decide +kernel

theorem checked_15488 : checkChunk representatives relations facts operations 15488 128 = true := by decide +kernel

theorem checked_15616 : checkChunk representatives relations facts operations 15616 128 = true := by decide +kernel

theorem checked_15744 : checkChunk representatives relations facts operations 15744 128 = true := by decide +kernel

theorem checked_15872 : checkChunk representatives relations facts operations 15872 128 = true := by decide +kernel

theorem checked_16000 : checkChunk representatives relations facts operations 16000 128 = true := by decide +kernel

theorem checked_16128 : checkChunk representatives relations facts operations 16128 128 = true := by decide +kernel

theorem checked_16256 : checkChunk representatives relations facts operations 16256 128 = true := by decide +kernel

theorem holds_block_15360 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 15360 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 16384 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h15360 := chunk_sound x representatives relations hr representatives_zero facts operations 15360 128 prior checked_15360

  have h15488 := chunk_sound x representatives relations hr representatives_zero facts operations 15488 128 h15360 checked_15488

  have h15616 := chunk_sound x representatives relations hr representatives_zero facts operations 15616 128 h15488 checked_15616

  have h15744 := chunk_sound x representatives relations hr representatives_zero facts operations 15744 128 h15616 checked_15744

  have h15872 := chunk_sound x representatives relations hr representatives_zero facts operations 15872 128 h15744 checked_15872

  have h16000 := chunk_sound x representatives relations hr representatives_zero facts operations 16000 128 h15872 checked_16000

  have h16128 := chunk_sound x representatives relations hr representatives_zero facts operations 16128 128 h16000 checked_16128

  have h16256 := chunk_sound x representatives relations hr representatives_zero facts operations 16256 128 h16128 checked_16256

  exact h16256

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
