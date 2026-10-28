module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_43008 : checkChunk representatives relations facts operations 43008 128 = true := by decide +kernel

theorem checked_43136 : checkChunk representatives relations facts operations 43136 128 = true := by decide +kernel

theorem checked_43264 : checkChunk representatives relations facts operations 43264 128 = true := by decide +kernel

theorem checked_43392 : checkChunk representatives relations facts operations 43392 128 = true := by decide +kernel

theorem checked_43520 : checkChunk representatives relations facts operations 43520 128 = true := by decide +kernel

theorem checked_43648 : checkChunk representatives relations facts operations 43648 128 = true := by decide +kernel

theorem checked_43776 : checkChunk representatives relations facts operations 43776 128 = true := by decide +kernel

theorem checked_43904 : checkChunk representatives relations facts operations 43904 128 = true := by decide +kernel

theorem holds_block_43008 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 43008 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 44032 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h43008 := chunk_sound x representatives relations hr representatives_zero facts operations 43008 128 prior checked_43008

  have h43136 := chunk_sound x representatives relations hr representatives_zero facts operations 43136 128 h43008 checked_43136

  have h43264 := chunk_sound x representatives relations hr representatives_zero facts operations 43264 128 h43136 checked_43264

  have h43392 := chunk_sound x representatives relations hr representatives_zero facts operations 43392 128 h43264 checked_43392

  have h43520 := chunk_sound x representatives relations hr representatives_zero facts operations 43520 128 h43392 checked_43520

  have h43648 := chunk_sound x representatives relations hr representatives_zero facts operations 43648 128 h43520 checked_43648

  have h43776 := chunk_sound x representatives relations hr representatives_zero facts operations 43776 128 h43648 checked_43776

  have h43904 := chunk_sound x representatives relations hr representatives_zero facts operations 43904 128 h43776 checked_43904

  exact h43904

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
