module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_66560 : checkChunk representatives relations facts operations 66560 128 = true := by decide +kernel

theorem checked_66688 : checkChunk representatives relations facts operations 66688 128 = true := by decide +kernel

theorem checked_66816 : checkChunk representatives relations facts operations 66816 128 = true := by decide +kernel

theorem checked_66944 : checkChunk representatives relations facts operations 66944 128 = true := by decide +kernel

theorem checked_67072 : checkChunk representatives relations facts operations 67072 128 = true := by decide +kernel

theorem checked_67200 : checkChunk representatives relations facts operations 67200 128 = true := by decide +kernel

theorem checked_67328 : checkChunk representatives relations facts operations 67328 128 = true := by decide +kernel

theorem checked_67456 : checkChunk representatives relations facts operations 67456 128 = true := by decide +kernel

theorem holds_block_66560 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 66560 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 67584 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h66560 := chunk_sound x representatives relations hr representatives_zero facts operations 66560 128 prior checked_66560

  have h66688 := chunk_sound x representatives relations hr representatives_zero facts operations 66688 128 h66560 checked_66688

  have h66816 := chunk_sound x representatives relations hr representatives_zero facts operations 66816 128 h66688 checked_66816

  have h66944 := chunk_sound x representatives relations hr representatives_zero facts operations 66944 128 h66816 checked_66944

  have h67072 := chunk_sound x representatives relations hr representatives_zero facts operations 67072 128 h66944 checked_67072

  have h67200 := chunk_sound x representatives relations hr representatives_zero facts operations 67200 128 h67072 checked_67200

  have h67328 := chunk_sound x representatives relations hr representatives_zero facts operations 67328 128 h67200 checked_67328

  have h67456 := chunk_sound x representatives relations hr representatives_zero facts operations 67456 128 h67328 checked_67456

  exact h67456

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
