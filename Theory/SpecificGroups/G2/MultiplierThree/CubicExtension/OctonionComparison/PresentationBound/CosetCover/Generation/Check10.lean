module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_10240 : checkChunk representatives relations facts operations 10240 128 = true := by decide +kernel

theorem checked_10368 : checkChunk representatives relations facts operations 10368 128 = true := by decide +kernel

theorem checked_10496 : checkChunk representatives relations facts operations 10496 128 = true := by decide +kernel

theorem checked_10624 : checkChunk representatives relations facts operations 10624 128 = true := by decide +kernel

theorem checked_10752 : checkChunk representatives relations facts operations 10752 128 = true := by decide +kernel

theorem checked_10880 : checkChunk representatives relations facts operations 10880 128 = true := by decide +kernel

theorem checked_11008 : checkChunk representatives relations facts operations 11008 128 = true := by decide +kernel

theorem checked_11136 : checkChunk representatives relations facts operations 11136 128 = true := by decide +kernel

theorem holds_block_10240 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 10240 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 11264 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h10240 := chunk_sound x representatives relations hr representatives_zero facts operations 10240 128 prior checked_10240

  have h10368 := chunk_sound x representatives relations hr representatives_zero facts operations 10368 128 h10240 checked_10368

  have h10496 := chunk_sound x representatives relations hr representatives_zero facts operations 10496 128 h10368 checked_10496

  have h10624 := chunk_sound x representatives relations hr representatives_zero facts operations 10624 128 h10496 checked_10624

  have h10752 := chunk_sound x representatives relations hr representatives_zero facts operations 10752 128 h10624 checked_10752

  have h10880 := chunk_sound x representatives relations hr representatives_zero facts operations 10880 128 h10752 checked_10880

  have h11008 := chunk_sound x representatives relations hr representatives_zero facts operations 11008 128 h10880 checked_11008

  have h11136 := chunk_sound x representatives relations hr representatives_zero facts operations 11136 128 h11008 checked_11136

  exact h11136

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
