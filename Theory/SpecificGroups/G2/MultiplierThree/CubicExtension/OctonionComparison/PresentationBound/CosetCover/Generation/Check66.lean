module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_67584 : checkChunk representatives relations facts operations 67584 128 = true := by decide +kernel

theorem checked_67712 : checkChunk representatives relations facts operations 67712 128 = true := by decide +kernel

theorem checked_67840 : checkChunk representatives relations facts operations 67840 128 = true := by decide +kernel

theorem checked_67968 : checkChunk representatives relations facts operations 67968 128 = true := by decide +kernel

theorem checked_68096 : checkChunk representatives relations facts operations 68096 128 = true := by decide +kernel

theorem checked_68224 : checkChunk representatives relations facts operations 68224 128 = true := by decide +kernel

theorem checked_68352 : checkChunk representatives relations facts operations 68352 128 = true := by decide +kernel

theorem checked_68480 : checkChunk representatives relations facts operations 68480 128 = true := by decide +kernel

theorem holds_block_67584 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 67584 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 68608 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h67584 := chunk_sound x representatives relations hr representatives_zero facts operations 67584 128 prior checked_67584

  have h67712 := chunk_sound x representatives relations hr representatives_zero facts operations 67712 128 h67584 checked_67712

  have h67840 := chunk_sound x representatives relations hr representatives_zero facts operations 67840 128 h67712 checked_67840

  have h67968 := chunk_sound x representatives relations hr representatives_zero facts operations 67968 128 h67840 checked_67968

  have h68096 := chunk_sound x representatives relations hr representatives_zero facts operations 68096 128 h67968 checked_68096

  have h68224 := chunk_sound x representatives relations hr representatives_zero facts operations 68224 128 h68096 checked_68224

  have h68352 := chunk_sound x representatives relations hr representatives_zero facts operations 68352 128 h68224 checked_68352

  have h68480 := chunk_sound x representatives relations hr representatives_zero facts operations 68480 128 h68352 checked_68480

  exact h68480

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
