module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_21504 : checkChunk representatives relations facts operations 21504 128 = true := by decide +kernel

theorem checked_21632 : checkChunk representatives relations facts operations 21632 128 = true := by decide +kernel

theorem checked_21760 : checkChunk representatives relations facts operations 21760 128 = true := by decide +kernel

theorem checked_21888 : checkChunk representatives relations facts operations 21888 128 = true := by decide +kernel

theorem checked_22016 : checkChunk representatives relations facts operations 22016 128 = true := by decide +kernel

theorem checked_22144 : checkChunk representatives relations facts operations 22144 128 = true := by decide +kernel

theorem checked_22272 : checkChunk representatives relations facts operations 22272 128 = true := by decide +kernel

theorem checked_22400 : checkChunk representatives relations facts operations 22400 128 = true := by decide +kernel

theorem holds_block_21504 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 21504 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 22528 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h21504 := chunk_sound x representatives relations hr representatives_zero facts operations 21504 128 prior checked_21504

  have h21632 := chunk_sound x representatives relations hr representatives_zero facts operations 21632 128 h21504 checked_21632

  have h21760 := chunk_sound x representatives relations hr representatives_zero facts operations 21760 128 h21632 checked_21760

  have h21888 := chunk_sound x representatives relations hr representatives_zero facts operations 21888 128 h21760 checked_21888

  have h22016 := chunk_sound x representatives relations hr representatives_zero facts operations 22016 128 h21888 checked_22016

  have h22144 := chunk_sound x representatives relations hr representatives_zero facts operations 22144 128 h22016 checked_22144

  have h22272 := chunk_sound x representatives relations hr representatives_zero facts operations 22272 128 h22144 checked_22272

  have h22400 := chunk_sound x representatives relations hr representatives_zero facts operations 22400 128 h22272 checked_22400

  exact h22400

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
