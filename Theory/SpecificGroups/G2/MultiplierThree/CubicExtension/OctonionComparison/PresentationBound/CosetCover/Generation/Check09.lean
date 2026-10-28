module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_9216 : checkChunk representatives relations facts operations 9216 128 = true := by decide +kernel

theorem checked_9344 : checkChunk representatives relations facts operations 9344 128 = true := by decide +kernel

theorem checked_9472 : checkChunk representatives relations facts operations 9472 128 = true := by decide +kernel

theorem checked_9600 : checkChunk representatives relations facts operations 9600 128 = true := by decide +kernel

theorem checked_9728 : checkChunk representatives relations facts operations 9728 128 = true := by decide +kernel

theorem checked_9856 : checkChunk representatives relations facts operations 9856 128 = true := by decide +kernel

theorem checked_9984 : checkChunk representatives relations facts operations 9984 128 = true := by decide +kernel

theorem checked_10112 : checkChunk representatives relations facts operations 10112 128 = true := by decide +kernel

theorem holds_block_9216 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 9216 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 10240 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h9216 := chunk_sound x representatives relations hr representatives_zero facts operations 9216 128 prior checked_9216

  have h9344 := chunk_sound x representatives relations hr representatives_zero facts operations 9344 128 h9216 checked_9344

  have h9472 := chunk_sound x representatives relations hr representatives_zero facts operations 9472 128 h9344 checked_9472

  have h9600 := chunk_sound x representatives relations hr representatives_zero facts operations 9600 128 h9472 checked_9600

  have h9728 := chunk_sound x representatives relations hr representatives_zero facts operations 9728 128 h9600 checked_9728

  have h9856 := chunk_sound x representatives relations hr representatives_zero facts operations 9856 128 h9728 checked_9856

  have h9984 := chunk_sound x representatives relations hr representatives_zero facts operations 9984 128 h9856 checked_9984

  have h10112 := chunk_sound x representatives relations hr representatives_zero facts operations 10112 128 h9984 checked_10112

  exact h10112

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
