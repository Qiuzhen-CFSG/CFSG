module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_41984 : checkChunk representatives relations facts operations 41984 128 = true := by decide +kernel

theorem checked_42112 : checkChunk representatives relations facts operations 42112 128 = true := by decide +kernel

theorem checked_42240 : checkChunk representatives relations facts operations 42240 128 = true := by decide +kernel

theorem checked_42368 : checkChunk representatives relations facts operations 42368 128 = true := by decide +kernel

theorem checked_42496 : checkChunk representatives relations facts operations 42496 128 = true := by decide +kernel

theorem checked_42624 : checkChunk representatives relations facts operations 42624 128 = true := by decide +kernel

theorem checked_42752 : checkChunk representatives relations facts operations 42752 128 = true := by decide +kernel

theorem checked_42880 : checkChunk representatives relations facts operations 42880 128 = true := by decide +kernel

theorem holds_block_41984 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 41984 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 43008 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h41984 := chunk_sound x representatives relations hr representatives_zero facts operations 41984 128 prior checked_41984

  have h42112 := chunk_sound x representatives relations hr representatives_zero facts operations 42112 128 h41984 checked_42112

  have h42240 := chunk_sound x representatives relations hr representatives_zero facts operations 42240 128 h42112 checked_42240

  have h42368 := chunk_sound x representatives relations hr representatives_zero facts operations 42368 128 h42240 checked_42368

  have h42496 := chunk_sound x representatives relations hr representatives_zero facts operations 42496 128 h42368 checked_42496

  have h42624 := chunk_sound x representatives relations hr representatives_zero facts operations 42624 128 h42496 checked_42624

  have h42752 := chunk_sound x representatives relations hr representatives_zero facts operations 42752 128 h42624 checked_42752

  have h42880 := chunk_sound x representatives relations hr representatives_zero facts operations 42880 128 h42752 checked_42880

  exact h42880

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
