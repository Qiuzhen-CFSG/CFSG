module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_16384 : checkChunk representatives relations facts operations 16384 128 = true := by decide +kernel

theorem checked_16512 : checkChunk representatives relations facts operations 16512 128 = true := by decide +kernel

theorem checked_16640 : checkChunk representatives relations facts operations 16640 128 = true := by decide +kernel

theorem checked_16768 : checkChunk representatives relations facts operations 16768 128 = true := by decide +kernel

theorem checked_16896 : checkChunk representatives relations facts operations 16896 128 = true := by decide +kernel

theorem checked_17024 : checkChunk representatives relations facts operations 17024 128 = true := by decide +kernel

theorem checked_17152 : checkChunk representatives relations facts operations 17152 128 = true := by decide +kernel

theorem checked_17280 : checkChunk representatives relations facts operations 17280 128 = true := by decide +kernel

theorem holds_block_16384 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 16384 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 17408 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h16384 := chunk_sound x representatives relations hr representatives_zero facts operations 16384 128 prior checked_16384

  have h16512 := chunk_sound x representatives relations hr representatives_zero facts operations 16512 128 h16384 checked_16512

  have h16640 := chunk_sound x representatives relations hr representatives_zero facts operations 16640 128 h16512 checked_16640

  have h16768 := chunk_sound x representatives relations hr representatives_zero facts operations 16768 128 h16640 checked_16768

  have h16896 := chunk_sound x representatives relations hr representatives_zero facts operations 16896 128 h16768 checked_16896

  have h17024 := chunk_sound x representatives relations hr representatives_zero facts operations 17024 128 h16896 checked_17024

  have h17152 := chunk_sound x representatives relations hr representatives_zero facts operations 17152 128 h17024 checked_17152

  have h17280 := chunk_sound x representatives relations hr representatives_zero facts operations 17280 128 h17152 checked_17280

  exact h17280

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
