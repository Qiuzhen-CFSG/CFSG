module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_45056 : checkChunk representatives relations facts operations 45056 128 = true := by decide +kernel

theorem checked_45184 : checkChunk representatives relations facts operations 45184 128 = true := by decide +kernel

theorem checked_45312 : checkChunk representatives relations facts operations 45312 128 = true := by decide +kernel

theorem checked_45440 : checkChunk representatives relations facts operations 45440 128 = true := by decide +kernel

theorem checked_45568 : checkChunk representatives relations facts operations 45568 128 = true := by decide +kernel

theorem checked_45696 : checkChunk representatives relations facts operations 45696 128 = true := by decide +kernel

theorem checked_45824 : checkChunk representatives relations facts operations 45824 128 = true := by decide +kernel

theorem checked_45952 : checkChunk representatives relations facts operations 45952 128 = true := by decide +kernel

theorem holds_block_45056 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 45056 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 46080 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h45056 := chunk_sound x representatives relations hr representatives_zero facts operations 45056 128 prior checked_45056

  have h45184 := chunk_sound x representatives relations hr representatives_zero facts operations 45184 128 h45056 checked_45184

  have h45312 := chunk_sound x representatives relations hr representatives_zero facts operations 45312 128 h45184 checked_45312

  have h45440 := chunk_sound x representatives relations hr representatives_zero facts operations 45440 128 h45312 checked_45440

  have h45568 := chunk_sound x representatives relations hr representatives_zero facts operations 45568 128 h45440 checked_45568

  have h45696 := chunk_sound x representatives relations hr representatives_zero facts operations 45696 128 h45568 checked_45696

  have h45824 := chunk_sound x representatives relations hr representatives_zero facts operations 45824 128 h45696 checked_45824

  have h45952 := chunk_sound x representatives relations hr representatives_zero facts operations 45952 128 h45824 checked_45952

  exact h45952

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
