module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_31744 : checkChunk representatives relations facts operations 31744 128 = true := by decide +kernel

theorem checked_31872 : checkChunk representatives relations facts operations 31872 128 = true := by decide +kernel

theorem checked_32000 : checkChunk representatives relations facts operations 32000 128 = true := by decide +kernel

theorem checked_32128 : checkChunk representatives relations facts operations 32128 128 = true := by decide +kernel

theorem checked_32256 : checkChunk representatives relations facts operations 32256 128 = true := by decide +kernel

theorem checked_32384 : checkChunk representatives relations facts operations 32384 128 = true := by decide +kernel

theorem checked_32512 : checkChunk representatives relations facts operations 32512 128 = true := by decide +kernel

theorem checked_32640 : checkChunk representatives relations facts operations 32640 128 = true := by decide +kernel

theorem holds_block_31744 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 31744 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 32768 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h31744 := chunk_sound x representatives relations hr representatives_zero facts operations 31744 128 prior checked_31744

  have h31872 := chunk_sound x representatives relations hr representatives_zero facts operations 31872 128 h31744 checked_31872

  have h32000 := chunk_sound x representatives relations hr representatives_zero facts operations 32000 128 h31872 checked_32000

  have h32128 := chunk_sound x representatives relations hr representatives_zero facts operations 32128 128 h32000 checked_32128

  have h32256 := chunk_sound x representatives relations hr representatives_zero facts operations 32256 128 h32128 checked_32256

  have h32384 := chunk_sound x representatives relations hr representatives_zero facts operations 32384 128 h32256 checked_32384

  have h32512 := chunk_sound x representatives relations hr representatives_zero facts operations 32512 128 h32384 checked_32512

  have h32640 := chunk_sound x representatives relations hr representatives_zero facts operations 32640 128 h32512 checked_32640

  exact h32640

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
