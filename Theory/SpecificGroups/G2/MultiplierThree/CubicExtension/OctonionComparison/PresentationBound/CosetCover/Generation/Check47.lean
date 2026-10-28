module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.CheckBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

theorem checked_48128 : checkChunk representatives relations facts operations 48128 128 = true := by decide +kernel

theorem checked_48256 : checkChunk representatives relations facts operations 48256 128 = true := by decide +kernel

theorem checked_48384 : checkChunk representatives relations facts operations 48384 128 = true := by decide +kernel

theorem checked_48512 : checkChunk representatives relations facts operations 48512 128 = true := by decide +kernel

theorem checked_48640 : checkChunk representatives relations facts operations 48640 128 = true := by decide +kernel

theorem checked_48768 : checkChunk representatives relations facts operations 48768 128 = true := by decide +kernel

theorem checked_48896 : checkChunk representatives relations facts operations 48896 128 = true := by decide +kernel

theorem checked_49024 : checkChunk representatives relations facts operations 49024 128 = true := by decide +kernel

theorem holds_block_48128 {G : Type*} [Group G] (x : Label → G)
    (hr : ∀ r, eval x (relations r) = 1)
    (prior : ∀ n, n < 48128 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n)) :
    ∀ n, n < 49152 → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (representatives i)) (facts n) := by

  have h48128 := chunk_sound x representatives relations hr representatives_zero facts operations 48128 128 prior checked_48128

  have h48256 := chunk_sound x representatives relations hr representatives_zero facts operations 48256 128 h48128 checked_48256

  have h48384 := chunk_sound x representatives relations hr representatives_zero facts operations 48384 128 h48256 checked_48384

  have h48512 := chunk_sound x representatives relations hr representatives_zero facts operations 48512 128 h48384 checked_48512

  have h48640 := chunk_sound x representatives relations hr representatives_zero facts operations 48640 128 h48512 checked_48640

  have h48768 := chunk_sound x representatives relations hr representatives_zero facts operations 48768 128 h48640 checked_48768

  have h48896 := chunk_sound x representatives relations hr representatives_zero facts operations 48896 128 h48768 checked_48896

  have h49024 := chunk_sound x representatives relations hr representatives_zero facts operations 49024 128 h48896 checked_49024

  exact h49024

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
