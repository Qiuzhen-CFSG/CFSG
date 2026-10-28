module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_55296 : checkChunk representatives relations facts operations 55296 128 = true := by decide +kernel

theorem checked_55424 : checkChunk representatives relations facts operations 55424 128 = true := by decide +kernel

theorem checked_55552 : checkChunk representatives relations facts operations 55552 128 = true := by decide +kernel

theorem checked_55680 : checkChunk representatives relations facts operations 55680 128 = true := by decide +kernel

theorem checked_55808 : checkChunk representatives relations facts operations 55808 128 = true := by decide +kernel

theorem checked_55936 : checkChunk representatives relations facts operations 55936 128 = true := by decide +kernel

theorem checked_56064 : checkChunk representatives relations facts operations 56064 128 = true := by decide +kernel

theorem checked_56192 : checkChunk representatives relations facts operations 56192 128 = true := by decide +kernel

theorem holds_block_55296 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 55296 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 56320 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h55296 := chunk_sound x representatives relations hr representatives_zero facts operations 55296 128 prior checked_55296

  have h55424 := chunk_sound x representatives relations hr representatives_zero facts operations 55424 128 h55296 checked_55424

  have h55552 := chunk_sound x representatives relations hr representatives_zero facts operations 55552 128 h55424 checked_55552

  have h55680 := chunk_sound x representatives relations hr representatives_zero facts operations 55680 128 h55552 checked_55680

  have h55808 := chunk_sound x representatives relations hr representatives_zero facts operations 55808 128 h55680 checked_55808

  have h55936 := chunk_sound x representatives relations hr representatives_zero facts operations 55936 128 h55808 checked_55936

  have h56064 := chunk_sound x representatives relations hr representatives_zero facts operations 56064 128 h55936 checked_56064

  have h56192 := chunk_sound x representatives relations hr representatives_zero facts operations 56192 128 h56064 checked_56192

  exact h56192

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
