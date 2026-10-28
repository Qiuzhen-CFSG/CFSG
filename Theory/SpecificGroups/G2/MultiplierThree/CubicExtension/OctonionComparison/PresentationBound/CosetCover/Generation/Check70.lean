module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_71680 : checkChunk representatives relations facts operations 71680 128 = true := by decide +kernel

theorem checked_71808 : checkChunk representatives relations facts operations 71808 128 = true := by decide +kernel

theorem checked_71936 : checkChunk representatives relations facts operations 71936 128 = true := by decide +kernel

theorem checked_72064 : checkChunk representatives relations facts operations 72064 128 = true := by decide +kernel

theorem checked_72192 : checkChunk representatives relations facts operations 72192 128 = true := by decide +kernel

theorem checked_72320 : checkChunk representatives relations facts operations 72320 128 = true := by decide +kernel

theorem checked_72448 : checkChunk representatives relations facts operations 72448 128 = true := by decide +kernel

theorem checked_72576 : checkChunk representatives relations facts operations 72576 128 = true := by decide +kernel

theorem holds_block_71680 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 71680 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 72704 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h71680 := chunk_sound x representatives relations hr representatives_zero facts operations 71680 128 prior checked_71680

  have h71808 := chunk_sound x representatives relations hr representatives_zero facts operations 71808 128 h71680 checked_71808

  have h71936 := chunk_sound x representatives relations hr representatives_zero facts operations 71936 128 h71808 checked_71936

  have h72064 := chunk_sound x representatives relations hr representatives_zero facts operations 72064 128 h71936 checked_72064

  have h72192 := chunk_sound x representatives relations hr representatives_zero facts operations 72192 128 h72064 checked_72192

  have h72320 := chunk_sound x representatives relations hr representatives_zero facts operations 72320 128 h72192 checked_72320

  have h72448 := chunk_sound x representatives relations hr representatives_zero facts operations 72448 128 h72320 checked_72448

  have h72576 := chunk_sound x representatives relations hr representatives_zero facts operations 72576 128 h72448 checked_72576

  exact h72576

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
