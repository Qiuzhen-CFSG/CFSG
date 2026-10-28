module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_39936 : checkChunk representatives relations facts operations 39936 128 = true := by decide +kernel

theorem checked_40064 : checkChunk representatives relations facts operations 40064 128 = true := by decide +kernel

theorem checked_40192 : checkChunk representatives relations facts operations 40192 128 = true := by decide +kernel

theorem checked_40320 : checkChunk representatives relations facts operations 40320 128 = true := by decide +kernel

theorem checked_40448 : checkChunk representatives relations facts operations 40448 128 = true := by decide +kernel

theorem checked_40576 : checkChunk representatives relations facts operations 40576 128 = true := by decide +kernel

theorem checked_40704 : checkChunk representatives relations facts operations 40704 128 = true := by decide +kernel

theorem checked_40832 : checkChunk representatives relations facts operations 40832 128 = true := by decide +kernel

theorem holds_block_39936 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 39936 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 40960 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h39936 := chunk_sound x representatives relations hr representatives_zero facts operations 39936 128 prior checked_39936

  have h40064 := chunk_sound x representatives relations hr representatives_zero facts operations 40064 128 h39936 checked_40064

  have h40192 := chunk_sound x representatives relations hr representatives_zero facts operations 40192 128 h40064 checked_40192

  have h40320 := chunk_sound x representatives relations hr representatives_zero facts operations 40320 128 h40192 checked_40320

  have h40448 := chunk_sound x representatives relations hr representatives_zero facts operations 40448 128 h40320 checked_40448

  have h40576 := chunk_sound x representatives relations hr representatives_zero facts operations 40576 128 h40448 checked_40576

  have h40704 := chunk_sound x representatives relations hr representatives_zero facts operations 40704 128 h40576 checked_40704

  have h40832 := chunk_sound x representatives relations hr representatives_zero facts operations 40832 128 h40704 checked_40832

  exact h40832

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
