module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_8192 : checkChunk representatives relations facts operations 8192 128 = true := by decide +kernel

theorem checked_8320 : checkChunk representatives relations facts operations 8320 128 = true := by decide +kernel

theorem checked_8448 : checkChunk representatives relations facts operations 8448 128 = true := by decide +kernel

theorem checked_8576 : checkChunk representatives relations facts operations 8576 128 = true := by decide +kernel

theorem checked_8704 : checkChunk representatives relations facts operations 8704 128 = true := by decide +kernel

theorem checked_8832 : checkChunk representatives relations facts operations 8832 128 = true := by decide +kernel

theorem checked_8960 : checkChunk representatives relations facts operations 8960 128 = true := by decide +kernel

theorem checked_9088 : checkChunk representatives relations facts operations 9088 128 = true := by decide +kernel

theorem holds_block_8192 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 8192 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 9216 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h8192 := chunk_sound x representatives relations hr representatives_zero facts operations 8192 128 prior checked_8192

  have h8320 := chunk_sound x representatives relations hr representatives_zero facts operations 8320 128 h8192 checked_8320

  have h8448 := chunk_sound x representatives relations hr representatives_zero facts operations 8448 128 h8320 checked_8448

  have h8576 := chunk_sound x representatives relations hr representatives_zero facts operations 8576 128 h8448 checked_8576

  have h8704 := chunk_sound x representatives relations hr representatives_zero facts operations 8704 128 h8576 checked_8704

  have h8832 := chunk_sound x representatives relations hr representatives_zero facts operations 8832 128 h8704 checked_8832

  have h8960 := chunk_sound x representatives relations hr representatives_zero facts operations 8960 128 h8832 checked_8960

  have h9088 := chunk_sound x representatives relations hr representatives_zero facts operations 9088 128 h8960 checked_9088

  exact h9088

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
