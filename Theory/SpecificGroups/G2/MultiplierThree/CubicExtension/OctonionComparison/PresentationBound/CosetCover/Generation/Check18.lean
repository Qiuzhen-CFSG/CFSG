module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_18432 : checkChunk representatives relations facts operations 18432 128 = true := by decide +kernel

theorem checked_18560 : checkChunk representatives relations facts operations 18560 128 = true := by decide +kernel

theorem checked_18688 : checkChunk representatives relations facts operations 18688 128 = true := by decide +kernel

theorem checked_18816 : checkChunk representatives relations facts operations 18816 128 = true := by decide +kernel

theorem checked_18944 : checkChunk representatives relations facts operations 18944 128 = true := by decide +kernel

theorem checked_19072 : checkChunk representatives relations facts operations 19072 128 = true := by decide +kernel

theorem checked_19200 : checkChunk representatives relations facts operations 19200 128 = true := by decide +kernel

theorem checked_19328 : checkChunk representatives relations facts operations 19328 128 = true := by decide +kernel

theorem holds_block_18432 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 18432 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 19456 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h18432 := chunk_sound x representatives relations hr representatives_zero facts operations 18432 128 prior checked_18432

  have h18560 := chunk_sound x representatives relations hr representatives_zero facts operations 18560 128 h18432 checked_18560

  have h18688 := chunk_sound x representatives relations hr representatives_zero facts operations 18688 128 h18560 checked_18688

  have h18816 := chunk_sound x representatives relations hr representatives_zero facts operations 18816 128 h18688 checked_18816

  have h18944 := chunk_sound x representatives relations hr representatives_zero facts operations 18944 128 h18816 checked_18944

  have h19072 := chunk_sound x representatives relations hr representatives_zero facts operations 19072 128 h18944 checked_19072

  have h19200 := chunk_sound x representatives relations hr representatives_zero facts operations 19200 128 h19072 checked_19200

  have h19328 := chunk_sound x representatives relations hr representatives_zero facts operations 19328 128 h19200 checked_19328

  exact h19328

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
