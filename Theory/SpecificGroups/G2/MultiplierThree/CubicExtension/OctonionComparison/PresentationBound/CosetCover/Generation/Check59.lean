module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_60416 : checkChunk representatives relations facts operations 60416 128 = true := by decide +kernel

theorem checked_60544 : checkChunk representatives relations facts operations 60544 128 = true := by decide +kernel

theorem checked_60672 : checkChunk representatives relations facts operations 60672 128 = true := by decide +kernel

theorem checked_60800 : checkChunk representatives relations facts operations 60800 128 = true := by decide +kernel

theorem checked_60928 : checkChunk representatives relations facts operations 60928 128 = true := by decide +kernel

theorem checked_61056 : checkChunk representatives relations facts operations 61056 128 = true := by decide +kernel

theorem checked_61184 : checkChunk representatives relations facts operations 61184 128 = true := by decide +kernel

theorem checked_61312 : checkChunk representatives relations facts operations 61312 128 = true := by decide +kernel

theorem holds_block_60416 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 60416 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 61440 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h60416 := chunk_sound x representatives relations hr representatives_zero facts operations 60416 128 prior checked_60416

  have h60544 := chunk_sound x representatives relations hr representatives_zero facts operations 60544 128 h60416 checked_60544

  have h60672 := chunk_sound x representatives relations hr representatives_zero facts operations 60672 128 h60544 checked_60672

  have h60800 := chunk_sound x representatives relations hr representatives_zero facts operations 60800 128 h60672 checked_60800

  have h60928 := chunk_sound x representatives relations hr representatives_zero facts operations 60928 128 h60800 checked_60928

  have h61056 := chunk_sound x representatives relations hr representatives_zero facts operations 61056 128 h60928 checked_61056

  have h61184 := chunk_sound x representatives relations hr representatives_zero facts operations 61184 128 h61056 checked_61184

  have h61312 := chunk_sound x representatives relations hr representatives_zero facts operations 61312 128 h61184 checked_61312

  exact h61312

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
