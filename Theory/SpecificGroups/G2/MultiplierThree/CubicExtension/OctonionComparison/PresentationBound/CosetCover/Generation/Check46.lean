module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_47104 : checkChunk representatives relations facts operations 47104 128 = true := by decide +kernel

theorem checked_47232 : checkChunk representatives relations facts operations 47232 128 = true := by decide +kernel

theorem checked_47360 : checkChunk representatives relations facts operations 47360 128 = true := by decide +kernel

theorem checked_47488 : checkChunk representatives relations facts operations 47488 128 = true := by decide +kernel

theorem checked_47616 : checkChunk representatives relations facts operations 47616 128 = true := by decide +kernel

theorem checked_47744 : checkChunk representatives relations facts operations 47744 128 = true := by decide +kernel

theorem checked_47872 : checkChunk representatives relations facts operations 47872 128 = true := by decide +kernel

theorem checked_48000 : checkChunk representatives relations facts operations 48000 128 = true := by decide +kernel

theorem holds_block_47104 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 47104 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 48128 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h47104 := chunk_sound x representatives relations hr representatives_zero facts operations 47104 128 prior checked_47104

  have h47232 := chunk_sound x representatives relations hr representatives_zero facts operations 47232 128 h47104 checked_47232

  have h47360 := chunk_sound x representatives relations hr representatives_zero facts operations 47360 128 h47232 checked_47360

  have h47488 := chunk_sound x representatives relations hr representatives_zero facts operations 47488 128 h47360 checked_47488

  have h47616 := chunk_sound x representatives relations hr representatives_zero facts operations 47616 128 h47488 checked_47616

  have h47744 := chunk_sound x representatives relations hr representatives_zero facts operations 47744 128 h47616 checked_47744

  have h47872 := chunk_sound x representatives relations hr representatives_zero facts operations 47872 128 h47744 checked_47872

  have h48000 := chunk_sound x representatives relations hr representatives_zero facts operations 48000 128 h47872 checked_48000

  exact h48000

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
