module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_69632 : checkChunk representatives relations facts operations 69632 128 = true := by decide +kernel

theorem checked_69760 : checkChunk representatives relations facts operations 69760 128 = true := by decide +kernel

theorem checked_69888 : checkChunk representatives relations facts operations 69888 128 = true := by decide +kernel

theorem checked_70016 : checkChunk representatives relations facts operations 70016 128 = true := by decide +kernel

theorem checked_70144 : checkChunk representatives relations facts operations 70144 128 = true := by decide +kernel

theorem checked_70272 : checkChunk representatives relations facts operations 70272 128 = true := by decide +kernel

theorem checked_70400 : checkChunk representatives relations facts operations 70400 128 = true := by decide +kernel

theorem checked_70528 : checkChunk representatives relations facts operations 70528 128 = true := by decide +kernel

theorem holds_block_69632 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 69632 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 70656 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h69632 := chunk_sound x representatives relations hr representatives_zero facts operations 69632 128 prior checked_69632

  have h69760 := chunk_sound x representatives relations hr representatives_zero facts operations 69760 128 h69632 checked_69760

  have h69888 := chunk_sound x representatives relations hr representatives_zero facts operations 69888 128 h69760 checked_69888

  have h70016 := chunk_sound x representatives relations hr representatives_zero facts operations 70016 128 h69888 checked_70016

  have h70144 := chunk_sound x representatives relations hr representatives_zero facts operations 70144 128 h70016 checked_70144

  have h70272 := chunk_sound x representatives relations hr representatives_zero facts operations 70272 128 h70144 checked_70272

  have h70400 := chunk_sound x representatives relations hr representatives_zero facts operations 70400 128 h70272 checked_70400

  have h70528 := chunk_sound x representatives relations hr representatives_zero facts operations 70528 128 h70400 checked_70528

  exact h70528

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
