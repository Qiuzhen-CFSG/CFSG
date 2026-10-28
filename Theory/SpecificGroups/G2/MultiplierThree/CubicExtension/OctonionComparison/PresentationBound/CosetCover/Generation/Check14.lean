module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_14336 : checkChunk representatives relations facts operations 14336 128 = true := by decide +kernel

theorem checked_14464 : checkChunk representatives relations facts operations 14464 128 = true := by decide +kernel

theorem checked_14592 : checkChunk representatives relations facts operations 14592 128 = true := by decide +kernel

theorem checked_14720 : checkChunk representatives relations facts operations 14720 128 = true := by decide +kernel

theorem checked_14848 : checkChunk representatives relations facts operations 14848 128 = true := by decide +kernel

theorem checked_14976 : checkChunk representatives relations facts operations 14976 128 = true := by decide +kernel

theorem checked_15104 : checkChunk representatives relations facts operations 15104 128 = true := by decide +kernel

theorem checked_15232 : checkChunk representatives relations facts operations 15232 128 = true := by decide +kernel

theorem holds_block_14336 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 14336 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 15360 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h14336 := chunk_sound x representatives relations hr representatives_zero facts operations 14336 128 prior checked_14336

  have h14464 := chunk_sound x representatives relations hr representatives_zero facts operations 14464 128 h14336 checked_14464

  have h14592 := chunk_sound x representatives relations hr representatives_zero facts operations 14592 128 h14464 checked_14592

  have h14720 := chunk_sound x representatives relations hr representatives_zero facts operations 14720 128 h14592 checked_14720

  have h14848 := chunk_sound x representatives relations hr representatives_zero facts operations 14848 128 h14720 checked_14848

  have h14976 := chunk_sound x representatives relations hr representatives_zero facts operations 14976 128 h14848 checked_14976

  have h15104 := chunk_sound x representatives relations hr representatives_zero facts operations 15104 128 h14976 checked_15104

  have h15232 := chunk_sound x representatives relations hr representatives_zero facts operations 15232 128 h15104 checked_15232

  exact h15232

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
