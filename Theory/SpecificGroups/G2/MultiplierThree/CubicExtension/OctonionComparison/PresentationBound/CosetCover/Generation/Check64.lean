module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_65536 : checkChunk representatives relations facts operations 65536 128 = true := by decide +kernel

theorem checked_65664 : checkChunk representatives relations facts operations 65664 128 = true := by decide +kernel

theorem checked_65792 : checkChunk representatives relations facts operations 65792 128 = true := by decide +kernel

theorem checked_65920 : checkChunk representatives relations facts operations 65920 128 = true := by decide +kernel

theorem checked_66048 : checkChunk representatives relations facts operations 66048 128 = true := by decide +kernel

theorem checked_66176 : checkChunk representatives relations facts operations 66176 128 = true := by decide +kernel

theorem checked_66304 : checkChunk representatives relations facts operations 66304 128 = true := by decide +kernel

theorem checked_66432 : checkChunk representatives relations facts operations 66432 128 = true := by decide +kernel

theorem holds_block_65536 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 65536 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 66560 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h65536 := chunk_sound x representatives relations hr representatives_zero facts operations 65536 128 prior checked_65536

  have h65664 := chunk_sound x representatives relations hr representatives_zero facts operations 65664 128 h65536 checked_65664

  have h65792 := chunk_sound x representatives relations hr representatives_zero facts operations 65792 128 h65664 checked_65792

  have h65920 := chunk_sound x representatives relations hr representatives_zero facts operations 65920 128 h65792 checked_65920

  have h66048 := chunk_sound x representatives relations hr representatives_zero facts operations 66048 128 h65920 checked_66048

  have h66176 := chunk_sound x representatives relations hr representatives_zero facts operations 66176 128 h66048 checked_66176

  have h66304 := chunk_sound x representatives relations hr representatives_zero facts operations 66304 128 h66176 checked_66304

  have h66432 := chunk_sound x representatives relations hr representatives_zero facts operations 66432 128 h66304 checked_66432

  exact h66432

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
