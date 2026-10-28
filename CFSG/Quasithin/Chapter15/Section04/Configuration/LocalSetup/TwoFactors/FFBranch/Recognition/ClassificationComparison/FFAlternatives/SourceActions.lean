module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceActions.Irreducible

/-!
# All six conclusions of B.5.1 on the original representation

The moved space and its central quotient are actual subrepresentations.
Every natural-module assertion has an intertwining linear equivalence and
an actual group equivalence; the natural-plus-dual action uses one actor
identification for both summands. Fixed spaces, direct sums, nonsplitting,
homogeneity and the Sylow-fixed-space centralizer are retained literally.

`QuasisimpleClassificationInput` is the universal implication for a chosen
class K. This module does not prove that classification theorem. Its proved
extraction only forgets module information from a supplied full conclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1,
printed pp.99–103; its irreducible cases refer to B.4.2, p.86.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- The possible natural extensions in B.5.1(1i). -/
def OuterNaturalAction : Prop :=
  (∃ n, 5 ≤ n ∧ n ≤ 8 ∧ IsSymmetricNatural ρ n) ∨
    Nonempty (ActionEquiv ρ (g2Natural (ZMod 2)))

/-- The full four-way alternative in B.5.1(1), after its Fitting equality.
The referenced B.4.2 data is on the actual quotient action. -/
inductive QuasisimpleActionCase (L : Subgroup D) (s : MovedSection ρ L) : Prop
  | irreducible (irrPlus : IsIrrPlus ρ L s.space.toSubmodule)
      (faithful : Function.Injective s.action)
      (irreducible : IsIrreducible (s.action.comp L.subtype))
      (source : IrreducibleActionCase s.action L (offenderSubgroup s.action))
      (extension : L = ⊤ ∨ (∀ T : Sylow 2 D, L ⊔ (T : Subgroup D) = ⊤) ∧
        OuterNaturalAction s.action)
  | doubleThree (F : BinaryField) (whole : L = ⊤)
      (e : ActionEquiv (s.space.toRepresentation.comp L.subtype)
        (repeated (linearNatural F 3) 2))
      (offenders : ∀ A, IsBestOffender s.space.toRepresentation A ↔
        IsFullAxisGroup F 3 ((A.subgroupOf L).map e.groupEquiv.toMonoidHom))
      (ratio : quadraticRatio ρ = 1)
  | naturalDual (d : ℕ) (degree : d = 4 ∨ d = 5) (whole : L = ⊤)
      (natural : IsNaturalPlusDual (s.space.toRepresentation.comp L.subtype) d)
  | repeatedNatural (d r : ℕ) (degree : d = 4 ∨ d = 5) (positive : 0 < r)
      (bound : r ≤ d - 1) (whole : L = ⊤)
      (natural : IsRepeatedLinearNatural
        (s.space.toRepresentation.comp L.subtype) BinaryField.two d r)

/-- Exactly the natural actions allowed in B.5.1(2). -/
inductive NonsplitNatural : Prop
  | linearTwo (F : BinaryField) (natural : IsLinearNatural ρ F 2)
  | symplectic (F : BinaryField) (natural : Nonempty (ActionEquiv ρ (binarySymplectic F)))
  | g2 (F : BinaryField) (natural : Nonempty (ActionEquiv ρ (binaryG2 F)))
  | alternatingSix (natural : IsAlternatingNatural ρ 6)
  | alternatingEight (natural : IsAlternatingNatural ρ 8)
  | derivedG2 (natural : Nonempty (ActionEquiv ρ (g2DerivedNatural (ZMod 2))))
  | linearThree (natural : IsLinearNatural ρ BinaryField.two 3)

/-- The shorter natural list in B.5.1(5). -/
inductive SupplementNatural : Prop
  | symplectic (F : BinaryField) (natural : Nonempty (ActionEquiv ρ (binarySymplectic F)))
  | alternatingSix (natural : IsAlternatingNatural ρ 6)
  | alternatingEight (natural : IsAlternatingNatural ρ 8)
  | linearThree (natural : IsLinearNatural ρ BinaryField.two 3)

/-- The full B.5.1 conclusion. Clause (5) is a supplement assertion; the
word hyperplane in B.5.6(5) is encoded separately there, not added here. -/
structure QuasisimpleSourceConclusion (L : Subgroup D) where
  sectionData : MovedSection ρ L
  fitting_eq : L = generalizedFitting D
  clause_one : QuasisimpleActionCase ρ L sectionData
  nonsplitting_iff :
    (¬ IsCompl sectionData.space.toSubmodule (fixedSpace ρ L)) ↔
      sectionData.space.toSubmodule ⊓ fixedSpace ρ L ≠ ⊥ ∨
      sectionData.space.toSubmodule ⊔ fixedSpace ρ L ≠ ⊤
  clause_two : ¬ IsCompl sectionData.space.toSubmodule (fixedSpace ρ L) →
    IsIrrPlus ρ L sectionData.space.toSubmodule ∧
      NonsplitNatural (sectionData.action.comp L.subtype)
  clause_three : IsHomogeneousAction (sectionData.action.comp L.subtype) ∨
    ∃ d, (d = 4 ∨ d = 5) ∧
      IsNaturalPlusDual (sectionData.space.toRepresentation.comp L.subtype) d
  clause_four : ¬ IsCompl sectionData.space.toSubmodule ρ.invariants →
    IsIrrPlus ρ L sectionData.space.toSubmodule ∧
      (¬ IsCompl sectionData.space.toSubmodule (fixedSpace ρ L) ∨
        (IsCompl sectionData.space.toSubmodule (fixedSpace ρ L) ∧
          (IsSymmetricNatural sectionData.space.toRepresentation 6 ∨
            IsSymmetricNatural sectionData.space.toRepresentation 8) ∧
          Nat.card ((fixedSpace ρ L) ⧸
            ρ.invariants.comap (fixedSpace ρ L).subtype) = 2))
  clause_five : sectionData.space.toSubmodule ⊔ ρ.invariants = ⊤ ∨
    (IsIrrPlus ρ L sectionData.space.toSubmodule ∧
      SupplementNatural (sectionData.action.comp L.subtype) ∧
      (Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) →
        sectionData.space.toSubmodule ⊓ fixedSpace ρ L = ⊥))
  clause_six : ∀ d, (d = 4 ∨ d = 5) → L = ⊤ →
    IsNaturalPlusDual (sectionData.space.toRepresentation.comp L.subtype) d →
      ∀ T : Sylow 2 D, Nonempty (SylowFixedCentralizer ρ L d T)

/-- Group-case extraction from the module list; no model premise is added. -/
theorem QuasisimpleActionCase.model {L : Subgroup D} {s : MovedSection ρ L}
    (h : QuasisimpleActionCase ρ L s) : QuasisimpleModel L := by
  cases h with
  | irreducible _ _ _ source _ => exact source.model _
  | doubleThree F _ e _ _ => exact .linearThree F e.groupEquiv
  | naturalDual d hd _ h =>
    obtain ⟨e⟩ := h
    rcases hd with rfl | rfl
    · exact .linearFourTwo e.groupEquiv
    · exact .linearFiveTwo e.groupEquiv
  | repeatedNatural d r hd _ _ _ h =>
    obtain ⟨e⟩ := h
    rcases hd with rfl | rfl
    · exact .linearFourTwo e.groupEquiv
    · exact .linearFiveTwo e.groupEquiv

/-- The model is about the literal generalized Fitting subgroup. -/
theorem QuasisimpleSourceConclusion.fittingModel {L : Subgroup D}
    (h : QuasisimpleSourceConclusion ρ L) : QuasisimpleModel (generalizedFitting D) := by
  rw [← h.fitting_eq]
  exact h.clause_one.model ρ

/-- The source hypotheses of B.5.1, with the chosen class K unchanged. -/
structure QuasisimpleSourceHypothesis (K : GroupClass.{u}) [Finite D]
    (L : Subgroup D) : Prop where
  finite_module : Module.Finite (ZMod 2) V
  faithful : Function.Injective ρ
  quasisimple : IsQuasisimple L
  sqtk : IsSQTK K L
  fitting : generalizedFitting D = L ⊔ center D
  twoCore : pCore 2 D = ⊥
  generated : offenderSubgroup ρ = ⊤

/-- The full universal B.5.1 implication; to be supplied by its theorem owner. -/
def QuasisimpleClassificationInput (K : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D]
    (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D),
    QuasisimpleSourceHypothesis ρ K L → Nonempty (QuasisimpleSourceConclusion ρ L)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
