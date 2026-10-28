module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_56320 : checkChunk representatives relations facts operations 56320 128 = true := by decide +kernel

theorem checked_56448 : checkChunk representatives relations facts operations 56448 128 = true := by decide +kernel

theorem checked_56576 : checkChunk representatives relations facts operations 56576 128 = true := by decide +kernel

theorem checked_56704 : checkChunk representatives relations facts operations 56704 128 = true := by decide +kernel

theorem checked_56832 : checkChunk representatives relations facts operations 56832 128 = true := by decide +kernel

theorem checked_56960 : checkChunk representatives relations facts operations 56960 128 = true := by decide +kernel

theorem checked_57088 : checkChunk representatives relations facts operations 57088 128 = true := by decide +kernel

theorem checked_57216 : checkChunk representatives relations facts operations 57216 128 = true := by decide +kernel

theorem holds_block_56320 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 56320 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 57344 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h56320 := chunk_sound x representatives relations hr representatives_zero facts operations 56320 128 prior checked_56320

  have h56448 := chunk_sound x representatives relations hr representatives_zero facts operations 56448 128 h56320 checked_56448

  have h56576 := chunk_sound x representatives relations hr representatives_zero facts operations 56576 128 h56448 checked_56576

  have h56704 := chunk_sound x representatives relations hr representatives_zero facts operations 56704 128 h56576 checked_56704

  have h56832 := chunk_sound x representatives relations hr representatives_zero facts operations 56832 128 h56704 checked_56832

  have h56960 := chunk_sound x representatives relations hr representatives_zero facts operations 56960 128 h56832 checked_56960

  have h57088 := chunk_sound x representatives relations hr representatives_zero facts operations 57088 128 h56960 checked_57088

  have h57216 := chunk_sound x representatives relations hr representatives_zero facts operations 57216 128 h57088 checked_57216

  exact h57216

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
