module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_19456 : checkChunk representatives relations facts operations 19456 128 = true := by decide +kernel

theorem checked_19584 : checkChunk representatives relations facts operations 19584 128 = true := by decide +kernel

theorem checked_19712 : checkChunk representatives relations facts operations 19712 128 = true := by decide +kernel

theorem checked_19840 : checkChunk representatives relations facts operations 19840 128 = true := by decide +kernel

theorem checked_19968 : checkChunk representatives relations facts operations 19968 128 = true := by decide +kernel

theorem checked_20096 : checkChunk representatives relations facts operations 20096 128 = true := by decide +kernel

theorem checked_20224 : checkChunk representatives relations facts operations 20224 128 = true := by decide +kernel

theorem checked_20352 : checkChunk representatives relations facts operations 20352 128 = true := by decide +kernel

theorem holds_block_19456 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 19456 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 20480 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h19456 := chunk_sound x representatives relations hr representatives_zero facts operations 19456 128 prior checked_19456

  have h19584 := chunk_sound x representatives relations hr representatives_zero facts operations 19584 128 h19456 checked_19584

  have h19712 := chunk_sound x representatives relations hr representatives_zero facts operations 19712 128 h19584 checked_19712

  have h19840 := chunk_sound x representatives relations hr representatives_zero facts operations 19840 128 h19712 checked_19840

  have h19968 := chunk_sound x representatives relations hr representatives_zero facts operations 19968 128 h19840 checked_19968

  have h20096 := chunk_sound x representatives relations hr representatives_zero facts operations 20096 128 h19968 checked_20096

  have h20224 := chunk_sound x representatives relations hr representatives_zero facts operations 20224 128 h20096 checked_20224

  have h20352 := chunk_sound x representatives relations hr representatives_zero facts operations 20352 128 h20224 checked_20352

  exact h20352

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
