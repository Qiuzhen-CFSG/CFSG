module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.BlockCandidates.Exhaustion

/-!
# Four group-theoretic candidates for the exceptional A₇ actors

This interface gives exhaustion and the converse for the literal block
stabilizer, pairwise distinctness, actual A₄ isomorphisms and the actual
quotients by two-cores. The intrinsic `PermittedActor` application keeps the
specified Sylow subgroup, action and plane. Its representation-dependent
commutator clause selects three actors in the separate plane calculation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.22, printed p.932.
-/

@[expose] public section
open Subgroup Equiv
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem permittedActor_four_candidates
    {ρ : Representation (ZMod 2) A7 W} {P : Submodule (ZMod 2) W}
    {S : Sylow 2 A7} {D : Subgroup A7}
    (hblock : Representation.BinaryOffender.subspaceStabilizer ρ P = blockStabilizer)
    (h : ExceptionalActors.PermittedActor ρ P S D) :
    D = cyclicActor ∨ D = naturalActor ∨ D = diagonalPlus ∨ D = diagonalMinus :=
  four_candidates S (hblock ▸ h.sylow_stabilizes) D (hblock ▸ h.stabilizes)
    h.normalized h.twoPerfect h.quotient_card

/-- All four candidates satisfy the group-theoretic actor conditions; normalization
holds for the entire block stabilizer. -/
theorem candidate_properties (D : Subgroup A7)
    (h : D = cyclicActor ∨ D = naturalActor ∨ D = diagonalPlus ∨ D = diagonalMinus) :
    D ≤ blockStabilizer ∧ blockStabilizer ≤ normalizer (D : Set A7) ∧
      IsPPerfect 2 D ∧ Nat.card (D ⧸ pCore 2 D) = 3 := by
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨cyclicActor_le_block, block_normalizes_cyclicActor,
      cyclicActor_twoPerfect, cyclicActor_quotient_card⟩
  · rw [← fourActor_zero]
    exact ⟨fourActor_le_block 0, block_normalizes_fourActor 0,
      fourActor_twoPerfect 0, fourActor_quotient_card 0⟩
  · rw [← fourActor_one]
    exact ⟨fourActor_le_block 1, block_normalizes_fourActor 1,
      fourActor_twoPerfect 1, fourActor_quotient_card 1⟩
  · rw [← fourActor_two]
    exact ⟨fourActor_le_block 2, block_normalizes_fourActor 2,
      fourActor_twoPerfect 2, fourActor_quotient_card 2⟩

theorem four_candidates_iff (S : Sylow 2 A7) (hS : (S : Subgroup A7) ≤ blockStabilizer)
    (D : Subgroup A7) :
    (D ≤ blockStabilizer ∧ (S : Subgroup A7) ≤ normalizer (D : Set A7) ∧
      IsPPerfect 2 D ∧ Nat.card (D ⧸ pCore 2 D) = 3) ↔
    D = cyclicActor ∨ D = naturalActor ∨ D = diagonalPlus ∨ D = diagonalMinus := by
  constructor
  · rintro ⟨hD, hn, hp, hq⟩
    exact four_candidates S hS D hD hn hp hq
  · intro h
    obtain ⟨hD, hn, hp, hq⟩ := candidate_properties D h
    exact ⟨hD, hS.trans hn, hp, hq⟩

/-- Pairwise distinctness of the literal subgroups, including both diagonal orientations. -/
theorem candidates_pairwise_distinct :
    cyclicActor ≠ naturalActor ∧ cyclicActor ≠ diagonalPlus ∧ cyclicActor ≠ diagonalMinus ∧
    naturalActor ≠ diagonalPlus ∧ naturalActor ≠ diagonalMinus ∧ diagonalPlus ≠ diagonalMinus := by
  have h01 : fourActor 0 ≠ fourActor 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (fourActor_injective h)
  have h02 : fourActor 0 ≠ fourActor 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (fourActor_injective h)
  have h12 : fourActor 1 ≠ fourActor 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (fourActor_injective h)
  simpa only [fourActor_zero, fourActor_one, fourActor_two] using
    And.intro (cyclicActor_ne_fourActor 0) (And.intro (cyclicActor_ne_fourActor 1)
      (And.intro (cyclicActor_ne_fourActor 2) (And.intro h01 (And.intro h02 h12))))

noncomputable def naturalActorEquiv : naturalActor ≃* alternatingGroup (Fin 4) := by
  rw [← fourActor_zero]
  exact (fourActorEquiv 0).symm
noncomputable def diagonalPlusEquiv : diagonalPlus ≃* alternatingGroup (Fin 4) := by
  rw [← fourActor_one]
  exact (fourActorEquiv 1).symm
noncomputable def diagonalMinusEquiv : diagonalMinus ≃* alternatingGroup (Fin 4) := by
  rw [← fourActor_two]
  exact (fourActorEquiv 2).symm

noncomputable def naturalActorQuotientEquiv :
    (naturalActor ⧸ pCore 2 naturalActor) ≃* Multiplicative (ZMod 3) := by
  rw [← fourActor_zero]
  exact fourActorQuotientEquiv 0
noncomputable def diagonalPlusQuotientEquiv :
    (diagonalPlus ⧸ pCore 2 diagonalPlus) ≃* Multiplicative (ZMod 3) := by
  rw [← fourActor_one]
  exact fourActorQuotientEquiv 1
noncomputable def diagonalMinusQuotientEquiv :
    (diagonalMinus ⧸ pCore 2 diagonalMinus) ≃* Multiplicative (ZMod 3) := by
  rw [← fourActor_two]
  exact fourActorQuotientEquiv 2

theorem candidate_twoCores :
    (pCore 2 naturalActor).map naturalActor.subtype = commonFour ∧
    (pCore 2 diagonalPlus).map diagonalPlus.subtype = commonFour ∧
    (pCore 2 diagonalMinus).map diagonalMinus.subtype = commonFour := by
  constructor
  · rw [← fourActor_zero]; exact fourActor_core 0
  constructor
  · rw [← fourActor_one]; exact fourActor_core 1
  · rw [← fourActor_two]; exact fourActor_core 2


/-- Conversely, a candidate with the required full plane commutator is an
actual permitted actor for the specified Sylow and plane. -/
theorem permittedActor_of_candidate
    {ρ : Representation (ZMod 2) A7 W} {P : Submodule (ZMod 2) W}
    {S : Sylow 2 A7} {D : Subgroup A7}
    (hblock : Representation.BinaryOffender.subspaceStabilizer ρ P = blockStabilizer)
    (hS : (S : Subgroup A7) ≤ blockStabilizer)
    (hD : D = cyclicActor ∨ D = naturalActor ∨ D = diagonalPlus ∨ D = diagonalMinus)
    (hcomm : Representation.BinaryOffender.subspaceCommutator ρ P D = P) :
    ExceptionalActors.PermittedActor ρ P S D := by
  obtain ⟨hd, hn, hp, hq⟩ := candidate_properties D hD
  exact ⟨hblock.symm ▸ hS, hblock.symm ▸ hd, hS.trans hn, hp, hq, hcomm⟩
/-- The orders of the four literal candidates. -/
theorem candidate_cards : Nat.card cyclicActor = 3 ∧ Nat.card naturalActor = 12 ∧
    Nat.card diagonalPlus = 12 ∧ Nat.card diagonalMinus = 12 := by
  refine ⟨cyclicActor_card, ?_, ?_, ?_⟩
  · rw [← fourActor_zero]; exact fourActor_card 0
  · rw [← fourActor_one]; exact fourActor_card 1
  · rw [← fourActor_two]; exact fourActor_card 2


end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue
