module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_12288 : checkChunk representatives relations facts operations 12288 128 = true := by decide +kernel

theorem checked_12416 : checkChunk representatives relations facts operations 12416 128 = true := by decide +kernel

theorem checked_12544 : checkChunk representatives relations facts operations 12544 128 = true := by decide +kernel

theorem checked_12672 : checkChunk representatives relations facts operations 12672 128 = true := by decide +kernel

theorem checked_12800 : checkChunk representatives relations facts operations 12800 128 = true := by decide +kernel

theorem checked_12928 : checkChunk representatives relations facts operations 12928 128 = true := by decide +kernel

theorem checked_13056 : checkChunk representatives relations facts operations 13056 128 = true := by decide +kernel

theorem checked_13184 : checkChunk representatives relations facts operations 13184 128 = true := by decide +kernel

theorem holds_block_12288 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 12288 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 13312 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h12288 := chunk_sound x representatives relations hr representatives_zero facts operations 12288 128 prior checked_12288

  have h12416 := chunk_sound x representatives relations hr representatives_zero facts operations 12416 128 h12288 checked_12416

  have h12544 := chunk_sound x representatives relations hr representatives_zero facts operations 12544 128 h12416 checked_12544

  have h12672 := chunk_sound x representatives relations hr representatives_zero facts operations 12672 128 h12544 checked_12672

  have h12800 := chunk_sound x representatives relations hr representatives_zero facts operations 12800 128 h12672 checked_12800

  have h12928 := chunk_sound x representatives relations hr representatives_zero facts operations 12928 128 h12800 checked_12928

  have h13056 := chunk_sound x representatives relations hr representatives_zero facts operations 13056 128 h12928 checked_13056

  have h13184 := chunk_sound x representatives relations hr representatives_zero facts operations 13184 128 h13056 checked_13184

  exact h13184

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
