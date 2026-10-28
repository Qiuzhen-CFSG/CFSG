module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_36864 : checkChunk representatives relations facts operations 36864 128 = true := by decide +kernel

theorem checked_36992 : checkChunk representatives relations facts operations 36992 128 = true := by decide +kernel

theorem checked_37120 : checkChunk representatives relations facts operations 37120 128 = true := by decide +kernel

theorem checked_37248 : checkChunk representatives relations facts operations 37248 128 = true := by decide +kernel

theorem checked_37376 : checkChunk representatives relations facts operations 37376 128 = true := by decide +kernel

theorem checked_37504 : checkChunk representatives relations facts operations 37504 128 = true := by decide +kernel

theorem checked_37632 : checkChunk representatives relations facts operations 37632 128 = true := by decide +kernel

theorem checked_37760 : checkChunk representatives relations facts operations 37760 128 = true := by decide +kernel

theorem holds_block_36864 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 36864 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 37888 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h36864 := chunk_sound x representatives relations hr representatives_zero facts operations 36864 128 prior checked_36864

  have h36992 := chunk_sound x representatives relations hr representatives_zero facts operations 36992 128 h36864 checked_36992

  have h37120 := chunk_sound x representatives relations hr representatives_zero facts operations 37120 128 h36992 checked_37120

  have h37248 := chunk_sound x representatives relations hr representatives_zero facts operations 37248 128 h37120 checked_37248

  have h37376 := chunk_sound x representatives relations hr representatives_zero facts operations 37376 128 h37248 checked_37376

  have h37504 := chunk_sound x representatives relations hr representatives_zero facts operations 37504 128 h37376 checked_37504

  have h37632 := chunk_sound x representatives relations hr representatives_zero facts operations 37632 128 h37504 checked_37632

  have h37760 := chunk_sound x representatives relations hr representatives_zero facts operations 37760 128 h37632 checked_37760

  exact h37760

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
