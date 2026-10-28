module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_33792 : checkChunk representatives relations facts operations 33792 128 = true := by decide +kernel

theorem checked_33920 : checkChunk representatives relations facts operations 33920 128 = true := by decide +kernel

theorem checked_34048 : checkChunk representatives relations facts operations 34048 128 = true := by decide +kernel

theorem checked_34176 : checkChunk representatives relations facts operations 34176 128 = true := by decide +kernel

theorem checked_34304 : checkChunk representatives relations facts operations 34304 128 = true := by decide +kernel

theorem checked_34432 : checkChunk representatives relations facts operations 34432 128 = true := by decide +kernel

theorem checked_34560 : checkChunk representatives relations facts operations 34560 128 = true := by decide +kernel

theorem checked_34688 : checkChunk representatives relations facts operations 34688 128 = true := by decide +kernel

theorem holds_block_33792 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 33792 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 34816 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h33792 := chunk_sound x representatives relations hr representatives_zero facts operations 33792 128 prior checked_33792

  have h33920 := chunk_sound x representatives relations hr representatives_zero facts operations 33920 128 h33792 checked_33920

  have h34048 := chunk_sound x representatives relations hr representatives_zero facts operations 34048 128 h33920 checked_34048

  have h34176 := chunk_sound x representatives relations hr representatives_zero facts operations 34176 128 h34048 checked_34176

  have h34304 := chunk_sound x representatives relations hr representatives_zero facts operations 34304 128 h34176 checked_34304

  have h34432 := chunk_sound x representatives relations hr representatives_zero facts operations 34432 128 h34304 checked_34432

  have h34560 := chunk_sound x representatives relations hr representatives_zero facts operations 34560 128 h34432 checked_34560

  have h34688 := chunk_sound x representatives relations hr representatives_zero facts operations 34688 128 h34560 checked_34688

  exact h34688

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
