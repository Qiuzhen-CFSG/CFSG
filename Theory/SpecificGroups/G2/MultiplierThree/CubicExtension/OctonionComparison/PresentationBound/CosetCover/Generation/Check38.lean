module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_38912 : checkChunk representatives relations facts operations 38912 128 = true := by decide +kernel

theorem checked_39040 : checkChunk representatives relations facts operations 39040 128 = true := by decide +kernel

theorem checked_39168 : checkChunk representatives relations facts operations 39168 128 = true := by decide +kernel

theorem checked_39296 : checkChunk representatives relations facts operations 39296 128 = true := by decide +kernel

theorem checked_39424 : checkChunk representatives relations facts operations 39424 128 = true := by decide +kernel

theorem checked_39552 : checkChunk representatives relations facts operations 39552 128 = true := by decide +kernel

theorem checked_39680 : checkChunk representatives relations facts operations 39680 128 = true := by decide +kernel

theorem checked_39808 : checkChunk representatives relations facts operations 39808 128 = true := by decide +kernel

theorem holds_block_38912 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 38912 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 39936 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h38912 := chunk_sound x representatives relations hr representatives_zero facts operations 38912 128 prior checked_38912

  have h39040 := chunk_sound x representatives relations hr representatives_zero facts operations 39040 128 h38912 checked_39040

  have h39168 := chunk_sound x representatives relations hr representatives_zero facts operations 39168 128 h39040 checked_39168

  have h39296 := chunk_sound x representatives relations hr representatives_zero facts operations 39296 128 h39168 checked_39296

  have h39424 := chunk_sound x representatives relations hr representatives_zero facts operations 39424 128 h39296 checked_39424

  have h39552 := chunk_sound x representatives relations hr representatives_zero facts operations 39552 128 h39424 checked_39552

  have h39680 := chunk_sound x representatives relations hr representatives_zero facts operations 39680 128 h39552 checked_39680

  have h39808 := chunk_sound x representatives relations hr representatives_zero facts operations 39808 128 h39680 checked_39808

  exact h39808

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
