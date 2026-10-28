module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_52224 : checkChunk representatives relations facts operations 52224 128 = true := by decide +kernel

theorem checked_52352 : checkChunk representatives relations facts operations 52352 128 = true := by decide +kernel

theorem checked_52480 : checkChunk representatives relations facts operations 52480 128 = true := by decide +kernel

theorem checked_52608 : checkChunk representatives relations facts operations 52608 128 = true := by decide +kernel

theorem checked_52736 : checkChunk representatives relations facts operations 52736 128 = true := by decide +kernel

theorem checked_52864 : checkChunk representatives relations facts operations 52864 128 = true := by decide +kernel

theorem checked_52992 : checkChunk representatives relations facts operations 52992 128 = true := by decide +kernel

theorem checked_53120 : checkChunk representatives relations facts operations 53120 128 = true := by decide +kernel

theorem holds_block_52224 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 52224 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 53248 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h52224 := chunk_sound x representatives relations hr representatives_zero facts operations 52224 128 prior checked_52224

  have h52352 := chunk_sound x representatives relations hr representatives_zero facts operations 52352 128 h52224 checked_52352

  have h52480 := chunk_sound x representatives relations hr representatives_zero facts operations 52480 128 h52352 checked_52480

  have h52608 := chunk_sound x representatives relations hr representatives_zero facts operations 52608 128 h52480 checked_52608

  have h52736 := chunk_sound x representatives relations hr representatives_zero facts operations 52736 128 h52608 checked_52736

  have h52864 := chunk_sound x representatives relations hr representatives_zero facts operations 52864 128 h52736 checked_52864

  have h52992 := chunk_sound x representatives relations hr representatives_zero facts operations 52992 128 h52864 checked_52992

  have h53120 := chunk_sound x representatives relations hr representatives_zero facts operations 53120 128 h52992 checked_53120

  exact h53120

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
