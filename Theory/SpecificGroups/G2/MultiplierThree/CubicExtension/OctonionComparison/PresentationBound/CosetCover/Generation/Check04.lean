module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_4096 : checkChunk representatives relations facts operations 4096 128 = true := by decide +kernel

theorem checked_4224 : checkChunk representatives relations facts operations 4224 128 = true := by decide +kernel

theorem checked_4352 : checkChunk representatives relations facts operations 4352 128 = true := by decide +kernel

theorem checked_4480 : checkChunk representatives relations facts operations 4480 128 = true := by decide +kernel

theorem checked_4608 : checkChunk representatives relations facts operations 4608 128 = true := by decide +kernel

theorem checked_4736 : checkChunk representatives relations facts operations 4736 128 = true := by decide +kernel

theorem checked_4864 : checkChunk representatives relations facts operations 4864 128 = true := by decide +kernel

theorem checked_4992 : checkChunk representatives relations facts operations 4992 128 = true := by decide +kernel

theorem holds_block_4096 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 4096 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 5120 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h4096 := chunk_sound x representatives relations hr representatives_zero facts operations 4096 128 prior checked_4096

  have h4224 := chunk_sound x representatives relations hr representatives_zero facts operations 4224 128 h4096 checked_4224

  have h4352 := chunk_sound x representatives relations hr representatives_zero facts operations 4352 128 h4224 checked_4352

  have h4480 := chunk_sound x representatives relations hr representatives_zero facts operations 4480 128 h4352 checked_4480

  have h4608 := chunk_sound x representatives relations hr representatives_zero facts operations 4608 128 h4480 checked_4608

  have h4736 := chunk_sound x representatives relations hr representatives_zero facts operations 4736 128 h4608 checked_4736

  have h4864 := chunk_sound x representatives relations hr representatives_zero facts operations 4864 128 h4736 checked_4864

  have h4992 := chunk_sound x representatives relations hr representatives_zero facts operations 4992 128 h4864 checked_4992

  exact h4992

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
