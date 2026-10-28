module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_49152 : checkChunk representatives relations facts operations 49152 128 = true := by decide +kernel

theorem checked_49280 : checkChunk representatives relations facts operations 49280 128 = true := by decide +kernel

theorem checked_49408 : checkChunk representatives relations facts operations 49408 128 = true := by decide +kernel

theorem checked_49536 : checkChunk representatives relations facts operations 49536 128 = true := by decide +kernel

theorem checked_49664 : checkChunk representatives relations facts operations 49664 128 = true := by decide +kernel

theorem checked_49792 : checkChunk representatives relations facts operations 49792 128 = true := by decide +kernel

theorem checked_49920 : checkChunk representatives relations facts operations 49920 128 = true := by decide +kernel

theorem checked_50048 : checkChunk representatives relations facts operations 50048 128 = true := by decide +kernel

theorem holds_block_49152 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 49152 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 50176 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h49152 := chunk_sound x representatives relations hr representatives_zero facts operations 49152 128 prior checked_49152

  have h49280 := chunk_sound x representatives relations hr representatives_zero facts operations 49280 128 h49152 checked_49280

  have h49408 := chunk_sound x representatives relations hr representatives_zero facts operations 49408 128 h49280 checked_49408

  have h49536 := chunk_sound x representatives relations hr representatives_zero facts operations 49536 128 h49408 checked_49536

  have h49664 := chunk_sound x representatives relations hr representatives_zero facts operations 49664 128 h49536 checked_49664

  have h49792 := chunk_sound x representatives relations hr representatives_zero facts operations 49792 128 h49664 checked_49792

  have h49920 := chunk_sound x representatives relations hr representatives_zero facts operations 49920 128 h49792 checked_49920

  have h50048 := chunk_sound x representatives relations hr representatives_zero facts operations 50048 128 h49920 checked_50048

  exact h50048

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
