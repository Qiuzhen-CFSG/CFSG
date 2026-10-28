module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_53248 : checkChunk representatives relations facts operations 53248 128 = true := by decide +kernel

theorem checked_53376 : checkChunk representatives relations facts operations 53376 128 = true := by decide +kernel

theorem checked_53504 : checkChunk representatives relations facts operations 53504 128 = true := by decide +kernel

theorem checked_53632 : checkChunk representatives relations facts operations 53632 128 = true := by decide +kernel

theorem checked_53760 : checkChunk representatives relations facts operations 53760 128 = true := by decide +kernel

theorem checked_53888 : checkChunk representatives relations facts operations 53888 128 = true := by decide +kernel

theorem checked_54016 : checkChunk representatives relations facts operations 54016 128 = true := by decide +kernel

theorem checked_54144 : checkChunk representatives relations facts operations 54144 128 = true := by decide +kernel

theorem holds_block_53248 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 53248 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 54272 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h53248 := chunk_sound x representatives relations hr representatives_zero facts operations 53248 128 prior checked_53248

  have h53376 := chunk_sound x representatives relations hr representatives_zero facts operations 53376 128 h53248 checked_53376

  have h53504 := chunk_sound x representatives relations hr representatives_zero facts operations 53504 128 h53376 checked_53504

  have h53632 := chunk_sound x representatives relations hr representatives_zero facts operations 53632 128 h53504 checked_53632

  have h53760 := chunk_sound x representatives relations hr representatives_zero facts operations 53760 128 h53632 checked_53760

  have h53888 := chunk_sound x representatives relations hr representatives_zero facts operations 53888 128 h53760 checked_53888

  have h54016 := chunk_sound x representatives relations hr representatives_zero facts operations 54016 128 h53888 checked_54016

  have h54144 := chunk_sound x representatives relations hr representatives_zero facts operations 54144 128 h54016 checked_54144

  exact h54144

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
