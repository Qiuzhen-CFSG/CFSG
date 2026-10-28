module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_5120 : checkChunk representatives relations facts operations 5120 128 = true := by decide +kernel

theorem checked_5248 : checkChunk representatives relations facts operations 5248 128 = true := by decide +kernel

theorem checked_5376 : checkChunk representatives relations facts operations 5376 128 = true := by decide +kernel

theorem checked_5504 : checkChunk representatives relations facts operations 5504 128 = true := by decide +kernel

theorem checked_5632 : checkChunk representatives relations facts operations 5632 128 = true := by decide +kernel

theorem checked_5760 : checkChunk representatives relations facts operations 5760 128 = true := by decide +kernel

theorem checked_5888 : checkChunk representatives relations facts operations 5888 128 = true := by decide +kernel

theorem checked_6016 : checkChunk representatives relations facts operations 6016 128 = true := by decide +kernel

theorem holds_block_5120 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 5120 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 6144 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h5120 := chunk_sound x representatives relations hr representatives_zero facts operations 5120 128 prior checked_5120

  have h5248 := chunk_sound x representatives relations hr representatives_zero facts operations 5248 128 h5120 checked_5248

  have h5376 := chunk_sound x representatives relations hr representatives_zero facts operations 5376 128 h5248 checked_5376

  have h5504 := chunk_sound x representatives relations hr representatives_zero facts operations 5504 128 h5376 checked_5504

  have h5632 := chunk_sound x representatives relations hr representatives_zero facts operations 5632 128 h5504 checked_5632

  have h5760 := chunk_sound x representatives relations hr representatives_zero facts operations 5760 128 h5632 checked_5760

  have h5888 := chunk_sound x representatives relations hr representatives_zero facts operations 5888 128 h5760 checked_5888

  have h6016 := chunk_sound x representatives relations hr representatives_zero facts operations 6016 128 h5888 checked_6016

  exact h6016

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
