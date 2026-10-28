module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_20480 : checkChunk representatives relations facts operations 20480 128 = true := by decide +kernel

theorem checked_20608 : checkChunk representatives relations facts operations 20608 128 = true := by decide +kernel

theorem checked_20736 : checkChunk representatives relations facts operations 20736 128 = true := by decide +kernel

theorem checked_20864 : checkChunk representatives relations facts operations 20864 128 = true := by decide +kernel

theorem checked_20992 : checkChunk representatives relations facts operations 20992 128 = true := by decide +kernel

theorem checked_21120 : checkChunk representatives relations facts operations 21120 128 = true := by decide +kernel

theorem checked_21248 : checkChunk representatives relations facts operations 21248 128 = true := by decide +kernel

theorem checked_21376 : checkChunk representatives relations facts operations 21376 128 = true := by decide +kernel

theorem holds_block_20480 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 20480 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 21504 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h20480 := chunk_sound x representatives relations hr representatives_zero facts operations 20480 128 prior checked_20480

  have h20608 := chunk_sound x representatives relations hr representatives_zero facts operations 20608 128 h20480 checked_20608

  have h20736 := chunk_sound x representatives relations hr representatives_zero facts operations 20736 128 h20608 checked_20736

  have h20864 := chunk_sound x representatives relations hr representatives_zero facts operations 20864 128 h20736 checked_20864

  have h20992 := chunk_sound x representatives relations hr representatives_zero facts operations 20992 128 h20864 checked_20992

  have h21120 := chunk_sound x representatives relations hr representatives_zero facts operations 21120 128 h20992 checked_21120

  have h21248 := chunk_sound x representatives relations hr representatives_zero facts operations 21248 128 h21120 checked_21248

  have h21376 := chunk_sound x representatives relations hr representatives_zero facts operations 21376 128 h21248 checked_21376

  exact h21376

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
