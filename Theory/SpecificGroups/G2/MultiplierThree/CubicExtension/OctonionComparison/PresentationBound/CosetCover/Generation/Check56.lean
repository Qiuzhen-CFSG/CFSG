module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_57344 : checkChunk representatives relations facts operations 57344 128 = true := by decide +kernel

theorem checked_57472 : checkChunk representatives relations facts operations 57472 128 = true := by decide +kernel

theorem checked_57600 : checkChunk representatives relations facts operations 57600 128 = true := by decide +kernel

theorem checked_57728 : checkChunk representatives relations facts operations 57728 128 = true := by decide +kernel

theorem checked_57856 : checkChunk representatives relations facts operations 57856 128 = true := by decide +kernel

theorem checked_57984 : checkChunk representatives relations facts operations 57984 128 = true := by decide +kernel

theorem checked_58112 : checkChunk representatives relations facts operations 58112 128 = true := by decide +kernel

theorem checked_58240 : checkChunk representatives relations facts operations 58240 128 = true := by decide +kernel

theorem holds_block_57344 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 57344 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 58368 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h57344 := chunk_sound x representatives relations hr representatives_zero facts operations 57344 128 prior checked_57344

  have h57472 := chunk_sound x representatives relations hr representatives_zero facts operations 57472 128 h57344 checked_57472

  have h57600 := chunk_sound x representatives relations hr representatives_zero facts operations 57600 128 h57472 checked_57600

  have h57728 := chunk_sound x representatives relations hr representatives_zero facts operations 57728 128 h57600 checked_57728

  have h57856 := chunk_sound x representatives relations hr representatives_zero facts operations 57856 128 h57728 checked_57856

  have h57984 := chunk_sound x representatives relations hr representatives_zero facts operations 57984 128 h57856 checked_57984

  have h58112 := chunk_sound x representatives relations hr representatives_zero facts operations 58112 128 h57984 checked_58112

  have h58240 := chunk_sound x representatives relations hr representatives_zero facts operations 58240 128 h58112 checked_58240

  exact h58240

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
