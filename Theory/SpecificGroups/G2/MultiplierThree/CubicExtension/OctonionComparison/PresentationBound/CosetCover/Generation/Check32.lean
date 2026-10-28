module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_32768 : checkChunk representatives relations facts operations 32768 128 = true := by decide +kernel

theorem checked_32896 : checkChunk representatives relations facts operations 32896 128 = true := by decide +kernel

theorem checked_33024 : checkChunk representatives relations facts operations 33024 128 = true := by decide +kernel

theorem checked_33152 : checkChunk representatives relations facts operations 33152 128 = true := by decide +kernel

theorem checked_33280 : checkChunk representatives relations facts operations 33280 128 = true := by decide +kernel

theorem checked_33408 : checkChunk representatives relations facts operations 33408 128 = true := by decide +kernel

theorem checked_33536 : checkChunk representatives relations facts operations 33536 128 = true := by decide +kernel

theorem checked_33664 : checkChunk representatives relations facts operations 33664 128 = true := by decide +kernel

theorem holds_block_32768 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 32768 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 33792 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h32768 := chunk_sound x representatives relations hr representatives_zero facts operations 32768 128 prior checked_32768

  have h32896 := chunk_sound x representatives relations hr representatives_zero facts operations 32896 128 h32768 checked_32896

  have h33024 := chunk_sound x representatives relations hr representatives_zero facts operations 33024 128 h32896 checked_33024

  have h33152 := chunk_sound x representatives relations hr representatives_zero facts operations 33152 128 h33024 checked_33152

  have h33280 := chunk_sound x representatives relations hr representatives_zero facts operations 33280 128 h33152 checked_33280

  have h33408 := chunk_sound x representatives relations hr representatives_zero facts operations 33408 128 h33280 checked_33408

  have h33536 := chunk_sound x representatives relations hr representatives_zero facts operations 33536 128 h33408 checked_33536

  have h33664 := chunk_sound x representatives relations hr representatives_zero facts operations 33664 128 h33536 checked_33664

  exact h33664

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
