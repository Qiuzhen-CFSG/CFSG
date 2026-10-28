module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_64512 : checkChunk representatives relations facts operations 64512 128 = true := by decide +kernel

theorem checked_64640 : checkChunk representatives relations facts operations 64640 128 = true := by decide +kernel

theorem checked_64768 : checkChunk representatives relations facts operations 64768 128 = true := by decide +kernel

theorem checked_64896 : checkChunk representatives relations facts operations 64896 128 = true := by decide +kernel

theorem checked_65024 : checkChunk representatives relations facts operations 65024 128 = true := by decide +kernel

theorem checked_65152 : checkChunk representatives relations facts operations 65152 128 = true := by decide +kernel

theorem checked_65280 : checkChunk representatives relations facts operations 65280 128 = true := by decide +kernel

theorem checked_65408 : checkChunk representatives relations facts operations 65408 128 = true := by decide +kernel

theorem holds_block_64512 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 64512 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 65536 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h64512 := chunk_sound x representatives relations hr representatives_zero facts operations 64512 128 prior checked_64512

  have h64640 := chunk_sound x representatives relations hr representatives_zero facts operations 64640 128 h64512 checked_64640

  have h64768 := chunk_sound x representatives relations hr representatives_zero facts operations 64768 128 h64640 checked_64768

  have h64896 := chunk_sound x representatives relations hr representatives_zero facts operations 64896 128 h64768 checked_64896

  have h65024 := chunk_sound x representatives relations hr representatives_zero facts operations 65024 128 h64896 checked_65024

  have h65152 := chunk_sound x representatives relations hr representatives_zero facts operations 65152 128 h65024 checked_65152

  have h65280 := chunk_sound x representatives relations hr representatives_zero facts operations 65280 128 h65152 checked_65280

  have h65408 := chunk_sound x representatives relations hr representatives_zero facts operations 65408 128 h65280 checked_65408

  exact h65408

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
