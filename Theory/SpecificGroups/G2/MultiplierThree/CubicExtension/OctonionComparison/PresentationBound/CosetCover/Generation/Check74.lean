module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_75776 : checkChunk representatives relations facts operations 75776 128 = true := by decide +kernel

theorem checked_75904 : checkChunk representatives relations facts operations 75904 128 = true := by decide +kernel

theorem checked_76032 : checkChunk representatives relations facts operations 76032 128 = true := by decide +kernel

theorem checked_76160 : checkChunk representatives relations facts operations 76160 128 = true := by decide +kernel

theorem checked_76288 : checkChunk representatives relations facts operations 76288 128 = true := by decide +kernel

theorem checked_76416 : checkChunk representatives relations facts operations 76416 128 = true := by decide +kernel

theorem checked_76544 : checkChunk representatives relations facts operations 76544 128 = true := by decide +kernel

theorem checked_76672 : checkChunk representatives relations facts operations 76672 31 = true := by decide +kernel

theorem holds_block_75776 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 75776 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 76703 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h75776 := chunk_sound x representatives relations hr representatives_zero facts operations 75776 128 prior checked_75776

  have h75904 := chunk_sound x representatives relations hr representatives_zero facts operations 75904 128 h75776 checked_75904

  have h76032 := chunk_sound x representatives relations hr representatives_zero facts operations 76032 128 h75904 checked_76032

  have h76160 := chunk_sound x representatives relations hr representatives_zero facts operations 76160 128 h76032 checked_76160

  have h76288 := chunk_sound x representatives relations hr representatives_zero facts operations 76288 128 h76160 checked_76288

  have h76416 := chunk_sound x representatives relations hr representatives_zero facts operations 76416 128 h76288 checked_76416

  have h76544 := chunk_sound x representatives relations hr representatives_zero facts operations 76544 128 h76416 checked_76544

  have h76672 := chunk_sound x representatives relations hr representatives_zero facts operations 76672 31 h76544 checked_76672

  exact h76672

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
