module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_68608 : checkChunk representatives relations facts operations 68608 128 = true := by decide +kernel

theorem checked_68736 : checkChunk representatives relations facts operations 68736 128 = true := by decide +kernel

theorem checked_68864 : checkChunk representatives relations facts operations 68864 128 = true := by decide +kernel

theorem checked_68992 : checkChunk representatives relations facts operations 68992 128 = true := by decide +kernel

theorem checked_69120 : checkChunk representatives relations facts operations 69120 128 = true := by decide +kernel

theorem checked_69248 : checkChunk representatives relations facts operations 69248 128 = true := by decide +kernel

theorem checked_69376 : checkChunk representatives relations facts operations 69376 128 = true := by decide +kernel

theorem checked_69504 : checkChunk representatives relations facts operations 69504 128 = true := by decide +kernel

theorem holds_block_68608 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 68608 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 69632 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h68608 := chunk_sound x representatives relations hr representatives_zero facts operations 68608 128 prior checked_68608

  have h68736 := chunk_sound x representatives relations hr representatives_zero facts operations 68736 128 h68608 checked_68736

  have h68864 := chunk_sound x representatives relations hr representatives_zero facts operations 68864 128 h68736 checked_68864

  have h68992 := chunk_sound x representatives relations hr representatives_zero facts operations 68992 128 h68864 checked_68992

  have h69120 := chunk_sound x representatives relations hr representatives_zero facts operations 69120 128 h68992 checked_69120

  have h69248 := chunk_sound x representatives relations hr representatives_zero facts operations 69248 128 h69120 checked_69248

  have h69376 := chunk_sound x representatives relations hr representatives_zero facts operations 69376 128 h69248 checked_69376

  have h69504 := chunk_sound x representatives relations hr representatives_zero facts operations 69504 128 h69376 checked_69504

  exact h69504

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
