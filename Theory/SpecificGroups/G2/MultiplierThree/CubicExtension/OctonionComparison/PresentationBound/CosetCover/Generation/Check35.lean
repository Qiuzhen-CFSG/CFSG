module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_35840 : checkChunk representatives relations facts operations 35840 128 = true := by decide +kernel

theorem checked_35968 : checkChunk representatives relations facts operations 35968 128 = true := by decide +kernel

theorem checked_36096 : checkChunk representatives relations facts operations 36096 128 = true := by decide +kernel

theorem checked_36224 : checkChunk representatives relations facts operations 36224 128 = true := by decide +kernel

theorem checked_36352 : checkChunk representatives relations facts operations 36352 128 = true := by decide +kernel

theorem checked_36480 : checkChunk representatives relations facts operations 36480 128 = true := by decide +kernel

theorem checked_36608 : checkChunk representatives relations facts operations 36608 128 = true := by decide +kernel

theorem checked_36736 : checkChunk representatives relations facts operations 36736 128 = true := by decide +kernel

theorem holds_block_35840 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 35840 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 36864 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h35840 := chunk_sound x representatives relations hr representatives_zero facts operations 35840 128 prior checked_35840

  have h35968 := chunk_sound x representatives relations hr representatives_zero facts operations 35968 128 h35840 checked_35968

  have h36096 := chunk_sound x representatives relations hr representatives_zero facts operations 36096 128 h35968 checked_36096

  have h36224 := chunk_sound x representatives relations hr representatives_zero facts operations 36224 128 h36096 checked_36224

  have h36352 := chunk_sound x representatives relations hr representatives_zero facts operations 36352 128 h36224 checked_36352

  have h36480 := chunk_sound x representatives relations hr representatives_zero facts operations 36480 128 h36352 checked_36480

  have h36608 := chunk_sound x representatives relations hr representatives_zero facts operations 36608 128 h36480 checked_36608

  have h36736 := chunk_sound x representatives relations hr representatives_zero facts operations 36736 128 h36608 checked_36736

  exact h36736

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
