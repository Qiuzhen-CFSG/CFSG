module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_58368 : checkChunk representatives relations facts operations 58368 128 = true := by decide +kernel

theorem checked_58496 : checkChunk representatives relations facts operations 58496 128 = true := by decide +kernel

theorem checked_58624 : checkChunk representatives relations facts operations 58624 128 = true := by decide +kernel

theorem checked_58752 : checkChunk representatives relations facts operations 58752 128 = true := by decide +kernel

theorem checked_58880 : checkChunk representatives relations facts operations 58880 128 = true := by decide +kernel

theorem checked_59008 : checkChunk representatives relations facts operations 59008 128 = true := by decide +kernel

theorem checked_59136 : checkChunk representatives relations facts operations 59136 128 = true := by decide +kernel

theorem checked_59264 : checkChunk representatives relations facts operations 59264 128 = true := by decide +kernel

theorem holds_block_58368 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 58368 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 59392 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h58368 := chunk_sound x representatives relations hr representatives_zero facts operations 58368 128 prior checked_58368

  have h58496 := chunk_sound x representatives relations hr representatives_zero facts operations 58496 128 h58368 checked_58496

  have h58624 := chunk_sound x representatives relations hr representatives_zero facts operations 58624 128 h58496 checked_58624

  have h58752 := chunk_sound x representatives relations hr representatives_zero facts operations 58752 128 h58624 checked_58752

  have h58880 := chunk_sound x representatives relations hr representatives_zero facts operations 58880 128 h58752 checked_58880

  have h59008 := chunk_sound x representatives relations hr representatives_zero facts operations 59008 128 h58880 checked_59008

  have h59136 := chunk_sound x representatives relations hr representatives_zero facts operations 59136 128 h59008 checked_59136

  have h59264 := chunk_sound x representatives relations hr representatives_zero facts operations 59264 128 h59136 checked_59264

  exact h59264

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
