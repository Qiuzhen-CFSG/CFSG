module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_40960 : checkChunk representatives relations facts operations 40960 128 = true := by decide +kernel

theorem checked_41088 : checkChunk representatives relations facts operations 41088 128 = true := by decide +kernel

theorem checked_41216 : checkChunk representatives relations facts operations 41216 128 = true := by decide +kernel

theorem checked_41344 : checkChunk representatives relations facts operations 41344 128 = true := by decide +kernel

theorem checked_41472 : checkChunk representatives relations facts operations 41472 128 = true := by decide +kernel

theorem checked_41600 : checkChunk representatives relations facts operations 41600 128 = true := by decide +kernel

theorem checked_41728 : checkChunk representatives relations facts operations 41728 128 = true := by decide +kernel

theorem checked_41856 : checkChunk representatives relations facts operations 41856 128 = true := by decide +kernel

theorem holds_block_40960 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 40960 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 41984 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h40960 := chunk_sound x representatives relations hr representatives_zero facts operations 40960 128 prior checked_40960

  have h41088 := chunk_sound x representatives relations hr representatives_zero facts operations 41088 128 h40960 checked_41088

  have h41216 := chunk_sound x representatives relations hr representatives_zero facts operations 41216 128 h41088 checked_41216

  have h41344 := chunk_sound x representatives relations hr representatives_zero facts operations 41344 128 h41216 checked_41344

  have h41472 := chunk_sound x representatives relations hr representatives_zero facts operations 41472 128 h41344 checked_41472

  have h41600 := chunk_sound x representatives relations hr representatives_zero facts operations 41600 128 h41472 checked_41600

  have h41728 := chunk_sound x representatives relations hr representatives_zero facts operations 41728 128 h41600 checked_41728

  have h41856 := chunk_sound x representatives relations hr representatives_zero facts operations 41856 128 h41728 checked_41856

  exact h41856

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
