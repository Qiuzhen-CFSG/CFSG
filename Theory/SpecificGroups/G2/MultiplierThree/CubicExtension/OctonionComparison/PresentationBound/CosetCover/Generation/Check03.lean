module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_3072 : checkChunk representatives relations facts operations 3072 128 = true := by decide +kernel

theorem checked_3200 : checkChunk representatives relations facts operations 3200 128 = true := by decide +kernel

theorem checked_3328 : checkChunk representatives relations facts operations 3328 128 = true := by decide +kernel

theorem checked_3456 : checkChunk representatives relations facts operations 3456 128 = true := by decide +kernel

theorem checked_3584 : checkChunk representatives relations facts operations 3584 128 = true := by decide +kernel

theorem checked_3712 : checkChunk representatives relations facts operations 3712 128 = true := by decide +kernel

theorem checked_3840 : checkChunk representatives relations facts operations 3840 128 = true := by decide +kernel

theorem checked_3968 : checkChunk representatives relations facts operations 3968 128 = true := by decide +kernel

theorem holds_block_3072 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 3072 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 4096 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h3072 := chunk_sound x representatives relations hr representatives_zero facts operations 3072 128 prior checked_3072

  have h3200 := chunk_sound x representatives relations hr representatives_zero facts operations 3200 128 h3072 checked_3200

  have h3328 := chunk_sound x representatives relations hr representatives_zero facts operations 3328 128 h3200 checked_3328

  have h3456 := chunk_sound x representatives relations hr representatives_zero facts operations 3456 128 h3328 checked_3456

  have h3584 := chunk_sound x representatives relations hr representatives_zero facts operations 3584 128 h3456 checked_3584

  have h3712 := chunk_sound x representatives relations hr representatives_zero facts operations 3712 128 h3584 checked_3712

  have h3840 := chunk_sound x representatives relations hr representatives_zero facts operations 3840 128 h3712 checked_3840

  have h3968 := chunk_sound x representatives relations hr representatives_zero facts operations 3968 128 h3840 checked_3968

  exact h3968

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
