module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_26624 : checkChunk representatives relations facts operations 26624 128 = true := by decide +kernel

theorem checked_26752 : checkChunk representatives relations facts operations 26752 128 = true := by decide +kernel

theorem checked_26880 : checkChunk representatives relations facts operations 26880 128 = true := by decide +kernel

theorem checked_27008 : checkChunk representatives relations facts operations 27008 128 = true := by decide +kernel

theorem checked_27136 : checkChunk representatives relations facts operations 27136 128 = true := by decide +kernel

theorem checked_27264 : checkChunk representatives relations facts operations 27264 128 = true := by decide +kernel

theorem checked_27392 : checkChunk representatives relations facts operations 27392 128 = true := by decide +kernel

theorem checked_27520 : checkChunk representatives relations facts operations 27520 128 = true := by decide +kernel

theorem holds_block_26624 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 26624 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 27648 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h26624 := chunk_sound x representatives relations hr representatives_zero facts operations 26624 128 prior checked_26624

  have h26752 := chunk_sound x representatives relations hr representatives_zero facts operations 26752 128 h26624 checked_26752

  have h26880 := chunk_sound x representatives relations hr representatives_zero facts operations 26880 128 h26752 checked_26880

  have h27008 := chunk_sound x representatives relations hr representatives_zero facts operations 27008 128 h26880 checked_27008

  have h27136 := chunk_sound x representatives relations hr representatives_zero facts operations 27136 128 h27008 checked_27136

  have h27264 := chunk_sound x representatives relations hr representatives_zero facts operations 27264 128 h27136 checked_27264

  have h27392 := chunk_sound x representatives relations hr representatives_zero facts operations 27392 128 h27264 checked_27392

  have h27520 := chunk_sound x representatives relations hr representatives_zero facts operations 27520 128 h27392 checked_27520

  exact h27520

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
