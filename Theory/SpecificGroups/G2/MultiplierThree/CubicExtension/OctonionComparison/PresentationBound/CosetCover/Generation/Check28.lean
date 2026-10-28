module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_28672 : checkChunk representatives relations facts operations 28672 128 = true := by decide +kernel

theorem checked_28800 : checkChunk representatives relations facts operations 28800 128 = true := by decide +kernel

theorem checked_28928 : checkChunk representatives relations facts operations 28928 128 = true := by decide +kernel

theorem checked_29056 : checkChunk representatives relations facts operations 29056 128 = true := by decide +kernel

theorem checked_29184 : checkChunk representatives relations facts operations 29184 128 = true := by decide +kernel

theorem checked_29312 : checkChunk representatives relations facts operations 29312 128 = true := by decide +kernel

theorem checked_29440 : checkChunk representatives relations facts operations 29440 128 = true := by decide +kernel

theorem checked_29568 : checkChunk representatives relations facts operations 29568 128 = true := by decide +kernel

theorem holds_block_28672 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 28672 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 29696 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h28672 := chunk_sound x representatives relations hr representatives_zero facts operations 28672 128 prior checked_28672

  have h28800 := chunk_sound x representatives relations hr representatives_zero facts operations 28800 128 h28672 checked_28800

  have h28928 := chunk_sound x representatives relations hr representatives_zero facts operations 28928 128 h28800 checked_28928

  have h29056 := chunk_sound x representatives relations hr representatives_zero facts operations 29056 128 h28928 checked_29056

  have h29184 := chunk_sound x representatives relations hr representatives_zero facts operations 29184 128 h29056 checked_29184

  have h29312 := chunk_sound x representatives relations hr representatives_zero facts operations 29312 128 h29184 checked_29312

  have h29440 := chunk_sound x representatives relations hr representatives_zero facts operations 29440 128 h29312 checked_29440

  have h29568 := chunk_sound x representatives relations hr representatives_zero facts operations 29568 128 h29440 checked_29568

  exact h29568

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
