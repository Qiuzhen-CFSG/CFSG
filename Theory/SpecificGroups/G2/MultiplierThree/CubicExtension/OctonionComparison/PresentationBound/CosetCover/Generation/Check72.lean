module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_73728 : checkChunk representatives relations facts operations 73728 128 = true := by decide +kernel

theorem checked_73856 : checkChunk representatives relations facts operations 73856 128 = true := by decide +kernel

theorem checked_73984 : checkChunk representatives relations facts operations 73984 128 = true := by decide +kernel

theorem checked_74112 : checkChunk representatives relations facts operations 74112 128 = true := by decide +kernel

theorem checked_74240 : checkChunk representatives relations facts operations 74240 128 = true := by decide +kernel

theorem checked_74368 : checkChunk representatives relations facts operations 74368 128 = true := by decide +kernel

theorem checked_74496 : checkChunk representatives relations facts operations 74496 128 = true := by decide +kernel

theorem checked_74624 : checkChunk representatives relations facts operations 74624 128 = true := by decide +kernel

theorem holds_block_73728 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 73728 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 74752 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h73728 := chunk_sound x representatives relations hr representatives_zero facts operations 73728 128 prior checked_73728

  have h73856 := chunk_sound x representatives relations hr representatives_zero facts operations 73856 128 h73728 checked_73856

  have h73984 := chunk_sound x representatives relations hr representatives_zero facts operations 73984 128 h73856 checked_73984

  have h74112 := chunk_sound x representatives relations hr representatives_zero facts operations 74112 128 h73984 checked_74112

  have h74240 := chunk_sound x representatives relations hr representatives_zero facts operations 74240 128 h74112 checked_74240

  have h74368 := chunk_sound x representatives relations hr representatives_zero facts operations 74368 128 h74240 checked_74368

  have h74496 := chunk_sound x representatives relations hr representatives_zero facts operations 74496 128 h74368 checked_74496

  have h74624 := chunk_sound x representatives relations hr representatives_zero facts operations 74624 128 h74496 checked_74624

  exact h74624

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
