module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_63488 : checkChunk representatives relations facts operations 63488 128 = true := by decide +kernel

theorem checked_63616 : checkChunk representatives relations facts operations 63616 128 = true := by decide +kernel

theorem checked_63744 : checkChunk representatives relations facts operations 63744 128 = true := by decide +kernel

theorem checked_63872 : checkChunk representatives relations facts operations 63872 128 = true := by decide +kernel

theorem checked_64000 : checkChunk representatives relations facts operations 64000 128 = true := by decide +kernel

theorem checked_64128 : checkChunk representatives relations facts operations 64128 128 = true := by decide +kernel

theorem checked_64256 : checkChunk representatives relations facts operations 64256 128 = true := by decide +kernel

theorem checked_64384 : checkChunk representatives relations facts operations 64384 128 = true := by decide +kernel

theorem holds_block_63488 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 63488 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 64512 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h63488 := chunk_sound x representatives relations hr representatives_zero facts operations 63488 128 prior checked_63488

  have h63616 := chunk_sound x representatives relations hr representatives_zero facts operations 63616 128 h63488 checked_63616

  have h63744 := chunk_sound x representatives relations hr representatives_zero facts operations 63744 128 h63616 checked_63744

  have h63872 := chunk_sound x representatives relations hr representatives_zero facts operations 63872 128 h63744 checked_63872

  have h64000 := chunk_sound x representatives relations hr representatives_zero facts operations 64000 128 h63872 checked_64000

  have h64128 := chunk_sound x representatives relations hr representatives_zero facts operations 64128 128 h64000 checked_64128

  have h64256 := chunk_sound x representatives relations hr representatives_zero facts operations 64256 128 h64128 checked_64256

  have h64384 := chunk_sound x representatives relations hr representatives_zero facts operations 64384 128 h64256 checked_64384

  exact h64384

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
