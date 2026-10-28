module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_30720 : checkChunk representatives relations facts operations 30720 128 = true := by decide +kernel

theorem checked_30848 : checkChunk representatives relations facts operations 30848 128 = true := by decide +kernel

theorem checked_30976 : checkChunk representatives relations facts operations 30976 128 = true := by decide +kernel

theorem checked_31104 : checkChunk representatives relations facts operations 31104 128 = true := by decide +kernel

theorem checked_31232 : checkChunk representatives relations facts operations 31232 128 = true := by decide +kernel

theorem checked_31360 : checkChunk representatives relations facts operations 31360 128 = true := by decide +kernel

theorem checked_31488 : checkChunk representatives relations facts operations 31488 128 = true := by decide +kernel

theorem checked_31616 : checkChunk representatives relations facts operations 31616 128 = true := by decide +kernel

theorem holds_block_30720 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 30720 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 31744 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h30720 := chunk_sound x representatives relations hr representatives_zero facts operations 30720 128 prior checked_30720

  have h30848 := chunk_sound x representatives relations hr representatives_zero facts operations 30848 128 h30720 checked_30848

  have h30976 := chunk_sound x representatives relations hr representatives_zero facts operations 30976 128 h30848 checked_30976

  have h31104 := chunk_sound x representatives relations hr representatives_zero facts operations 31104 128 h30976 checked_31104

  have h31232 := chunk_sound x representatives relations hr representatives_zero facts operations 31232 128 h31104 checked_31232

  have h31360 := chunk_sound x representatives relations hr representatives_zero facts operations 31360 128 h31232 checked_31360

  have h31488 := chunk_sound x representatives relations hr representatives_zero facts operations 31488 128 h31360 checked_31488

  have h31616 := chunk_sound x representatives relations hr representatives_zero facts operations 31616 128 h31488 checked_31616

  exact h31616

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
