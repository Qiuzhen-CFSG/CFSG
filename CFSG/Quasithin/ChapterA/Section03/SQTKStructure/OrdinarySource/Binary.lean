module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Basic
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Alternating
public import Theory.SpecificGroups.PSL4Two.SchurMultiplier
public import Theory.SpecificGroups.PSL5Two.UniversalCover
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.SpecificGroups.G2.MultiplierTwoGroup
public section
/-!
# Binary and even rank-two ordinary components in A.3.6

The A₈ exceptional isomorphism handles PSL₄(2). The checked PSL₅(2),
symplectic and G₂ universal-kernel calculations make the marked central
quotient an isomorphism, so each branch supplies the full common A.3.6
conclusion and its exact Theorem C model.

Source: Aschbacher–Smith A.3.6 and I.1.3, printed pp.43–45, 407.
-/

noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.SQTKStructure.OrdinarySource
open Chapter1.Section02 Chapter1.Section02.LocalModels

/-- The binary degree-four case is the actual A₈ case. -/
theorem a36_psl4_two {X : Type*} [Group X] [Finite X]
    (hcore : pCore 2 X = ⊥) (L : Subgroup X) (hL : IsComponent X L)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = 2)
    (e : L ⧸ center L ≃* PSL(4,F)) : A36Conclusion L :=
  a36_alternating hcore L hL 8 (by decide)
    (e.trans (Matrix.PSL4Two.binaryEquivAlternatingEight F hF))

/-- The genuine binary degree-five multiplier makes the marked projection
an isomorphism of the entire component. -/
theorem a36_psl5_two {X : Type*} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = 2)
    (e : L ⧸ center L ≃* PSL(5,F)) : A36Conclusion L := by
  apply conclusion_of_universal_two_kernel L hL hcore e
  · rw [Theory.SpecificGroups.PSL5Two.UniversalCover.field_universalProjection_ker_eq_bot F hF]
    exact IsPGroup.of_card (n := 0) (by simp)
  · intro j
    exact .binary_linear 5 (Or.inr rfl) ⟨F, inferInstance, inferInstance, hF, ⟨j⟩⟩

/-- The full even symplectic four-space branch, with the original PSp model. -/
theorem a36_symplectic_even {X : Type*} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L)
    (n : ℕ) (hn : 2 ≤ n) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n)
    (e : L ⧸ center L ≃* ClassicalGroup.PSp 2 F) : A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let t := Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)
  obtain ⟨j, _⟩ := Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.exists_whole_model
    hF (by omega) (e.trans t.symm)
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup (ClassicalGroup.PSp 2 F) := e.symm.isSimpleGroup
  let : IsSimpleGroup L := (j.trans t).isSimpleGroup
  exact simple_conclusion L hL
    (.rank_two (.symplectic n hn ⟨F, inferInstance, inferInstance, hF, ⟨j.trans t⟩⟩))

/-- Two-primary kernel control suffices for every permitted even G₂ field,
including the exceptional four-element field. -/
theorem a36_g2_even {X : Type*} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (n : ℕ) (hn : 2 ≤ n) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n)
    (e : L ⧸ center L ≃* Atlas.G2.Model F) : A36Conclusion L := by
  apply conclusion_of_universal_two_kernel L hL hcore e
    (Atlas.G2.FiniteCover.universalKernel_isPGroup_of_card_pow hF (by omega))
  intro j
  exact .rank_two (.g2 n hn ⟨F, inferInstance, inferInstance, hF, ⟨j⟩⟩)
end CFSG.Quasithin.ChapterA.SQTKStructure.OrdinarySource
