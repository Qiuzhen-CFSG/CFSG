module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_72704 : checkChunk representatives relations facts operations 72704 128 = true := by decide +kernel

theorem checked_72832 : checkChunk representatives relations facts operations 72832 128 = true := by decide +kernel

theorem checked_72960 : checkChunk representatives relations facts operations 72960 128 = true := by decide +kernel

theorem checked_73088 : checkChunk representatives relations facts operations 73088 128 = true := by decide +kernel

theorem checked_73216 : checkChunk representatives relations facts operations 73216 128 = true := by decide +kernel

theorem checked_73344 : checkChunk representatives relations facts operations 73344 128 = true := by decide +kernel

theorem checked_73472 : checkChunk representatives relations facts operations 73472 128 = true := by decide +kernel

theorem checked_73600 : checkChunk representatives relations facts operations 73600 128 = true := by decide +kernel

theorem holds_block_72704 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 72704 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 73728 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h72704 := chunk_sound x representatives relations hr representatives_zero facts operations 72704 128 prior checked_72704

  have h72832 := chunk_sound x representatives relations hr representatives_zero facts operations 72832 128 h72704 checked_72832

  have h72960 := chunk_sound x representatives relations hr representatives_zero facts operations 72960 128 h72832 checked_72960

  have h73088 := chunk_sound x representatives relations hr representatives_zero facts operations 73088 128 h72960 checked_73088

  have h73216 := chunk_sound x representatives relations hr representatives_zero facts operations 73216 128 h73088 checked_73216

  have h73344 := chunk_sound x representatives relations hr representatives_zero facts operations 73344 128 h73216 checked_73344

  have h73472 := chunk_sound x representatives relations hr representatives_zero facts operations 73472 128 h73344 checked_73472

  have h73600 := chunk_sound x representatives relations hr representatives_zero facts operations 73600 128 h73472 checked_73600

  exact h73600

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
