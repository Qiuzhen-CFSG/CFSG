module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_0 : checkChunk representatives relations facts operations 0 128 = true := by decide +kernel

theorem checked_128 : checkChunk representatives relations facts operations 128 128 = true := by decide +kernel

theorem checked_256 : checkChunk representatives relations facts operations 256 128 = true := by decide +kernel

theorem checked_384 : checkChunk representatives relations facts operations 384 128 = true := by decide +kernel

theorem checked_512 : checkChunk representatives relations facts operations 512 128 = true := by decide +kernel

theorem checked_640 : checkChunk representatives relations facts operations 640 128 = true := by decide +kernel

theorem checked_768 : checkChunk representatives relations facts operations 768 128 = true := by decide +kernel

theorem checked_896 : checkChunk representatives relations facts operations 896 128 = true := by decide +kernel

theorem holds_block_0 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 0 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 1024 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h0 := chunk_sound x representatives relations hr representatives_zero facts operations 0 128 prior checked_0

  have h128 := chunk_sound x representatives relations hr representatives_zero facts operations 128 128 h0 checked_128

  have h256 := chunk_sound x representatives relations hr representatives_zero facts operations 256 128 h128 checked_256

  have h384 := chunk_sound x representatives relations hr representatives_zero facts operations 384 128 h256 checked_384

  have h512 := chunk_sound x representatives relations hr representatives_zero facts operations 512 128 h384 checked_512

  have h640 := chunk_sound x representatives relations hr representatives_zero facts operations 640 128 h512 checked_640

  have h768 := chunk_sound x representatives relations hr representatives_zero facts operations 768 128 h640 checked_768

  have h896 := chunk_sound x representatives relations hr representatives_zero facts operations 896 128 h768 checked_896

  exact h896

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
