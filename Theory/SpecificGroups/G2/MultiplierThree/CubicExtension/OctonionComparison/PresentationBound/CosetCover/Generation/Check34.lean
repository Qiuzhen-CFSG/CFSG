module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_34816 : checkChunk representatives relations facts operations 34816 128 = true := by decide +kernel

theorem checked_34944 : checkChunk representatives relations facts operations 34944 128 = true := by decide +kernel

theorem checked_35072 : checkChunk representatives relations facts operations 35072 128 = true := by decide +kernel

theorem checked_35200 : checkChunk representatives relations facts operations 35200 128 = true := by decide +kernel

theorem checked_35328 : checkChunk representatives relations facts operations 35328 128 = true := by decide +kernel

theorem checked_35456 : checkChunk representatives relations facts operations 35456 128 = true := by decide +kernel

theorem checked_35584 : checkChunk representatives relations facts operations 35584 128 = true := by decide +kernel

theorem checked_35712 : checkChunk representatives relations facts operations 35712 128 = true := by decide +kernel

theorem holds_block_34816 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 34816 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 35840 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h34816 := chunk_sound x representatives relations hr representatives_zero facts operations 34816 128 prior checked_34816

  have h34944 := chunk_sound x representatives relations hr representatives_zero facts operations 34944 128 h34816 checked_34944

  have h35072 := chunk_sound x representatives relations hr representatives_zero facts operations 35072 128 h34944 checked_35072

  have h35200 := chunk_sound x representatives relations hr representatives_zero facts operations 35200 128 h35072 checked_35200

  have h35328 := chunk_sound x representatives relations hr representatives_zero facts operations 35328 128 h35200 checked_35328

  have h35456 := chunk_sound x representatives relations hr representatives_zero facts operations 35456 128 h35328 checked_35456

  have h35584 := chunk_sound x representatives relations hr representatives_zero facts operations 35584 128 h35456 checked_35584

  have h35712 := chunk_sound x representatives relations hr representatives_zero facts operations 35712 128 h35584 checked_35712

  exact h35712

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
