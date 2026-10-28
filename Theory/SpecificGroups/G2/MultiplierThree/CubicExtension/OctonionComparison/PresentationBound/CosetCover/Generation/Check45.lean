module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_46080 : checkChunk representatives relations facts operations 46080 128 = true := by decide +kernel

theorem checked_46208 : checkChunk representatives relations facts operations 46208 128 = true := by decide +kernel

theorem checked_46336 : checkChunk representatives relations facts operations 46336 128 = true := by decide +kernel

theorem checked_46464 : checkChunk representatives relations facts operations 46464 128 = true := by decide +kernel

theorem checked_46592 : checkChunk representatives relations facts operations 46592 128 = true := by decide +kernel

theorem checked_46720 : checkChunk representatives relations facts operations 46720 128 = true := by decide +kernel

theorem checked_46848 : checkChunk representatives relations facts operations 46848 128 = true := by decide +kernel

theorem checked_46976 : checkChunk representatives relations facts operations 46976 128 = true := by decide +kernel

theorem holds_block_46080 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 46080 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 47104 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h46080 := chunk_sound x representatives relations hr representatives_zero facts operations 46080 128 prior checked_46080

  have h46208 := chunk_sound x representatives relations hr representatives_zero facts operations 46208 128 h46080 checked_46208

  have h46336 := chunk_sound x representatives relations hr representatives_zero facts operations 46336 128 h46208 checked_46336

  have h46464 := chunk_sound x representatives relations hr representatives_zero facts operations 46464 128 h46336 checked_46464

  have h46592 := chunk_sound x representatives relations hr representatives_zero facts operations 46592 128 h46464 checked_46592

  have h46720 := chunk_sound x representatives relations hr representatives_zero facts operations 46720 128 h46592 checked_46720

  have h46848 := chunk_sound x representatives relations hr representatives_zero facts operations 46848 128 h46720 checked_46848

  have h46976 := chunk_sound x representatives relations hr representatives_zero facts operations 46976 128 h46848 checked_46976

  exact h46976

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
