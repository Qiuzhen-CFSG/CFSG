module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_11264 : checkChunk representatives relations facts operations 11264 128 = true := by decide +kernel

theorem checked_11392 : checkChunk representatives relations facts operations 11392 128 = true := by decide +kernel

theorem checked_11520 : checkChunk representatives relations facts operations 11520 128 = true := by decide +kernel

theorem checked_11648 : checkChunk representatives relations facts operations 11648 128 = true := by decide +kernel

theorem checked_11776 : checkChunk representatives relations facts operations 11776 128 = true := by decide +kernel

theorem checked_11904 : checkChunk representatives relations facts operations 11904 128 = true := by decide +kernel

theorem checked_12032 : checkChunk representatives relations facts operations 12032 128 = true := by decide +kernel

theorem checked_12160 : checkChunk representatives relations facts operations 12160 128 = true := by decide +kernel

theorem holds_block_11264 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 11264 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 12288 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h11264 := chunk_sound x representatives relations hr representatives_zero facts operations 11264 128 prior checked_11264

  have h11392 := chunk_sound x representatives relations hr representatives_zero facts operations 11392 128 h11264 checked_11392

  have h11520 := chunk_sound x representatives relations hr representatives_zero facts operations 11520 128 h11392 checked_11520

  have h11648 := chunk_sound x representatives relations hr representatives_zero facts operations 11648 128 h11520 checked_11648

  have h11776 := chunk_sound x representatives relations hr representatives_zero facts operations 11776 128 h11648 checked_11776

  have h11904 := chunk_sound x representatives relations hr representatives_zero facts operations 11904 128 h11776 checked_11904

  have h12032 := chunk_sound x representatives relations hr representatives_zero facts operations 12032 128 h11904 checked_12032

  have h12160 := chunk_sound x representatives relations hr representatives_zero facts operations 12160 128 h12032 checked_12160

  exact h12160

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
