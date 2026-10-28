module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Irreducible
public import Theory.GroupTheory.GeneralizedFitting.Defs

/-!
# Native source statement for all six clauses of B.5.1

The finite faithful binary action, actual generalized Fitting subgroup, and
chosen K-class are unchanged. All six conclusions retain their literal
moved/fixed spaces and compatible action identifications. Clause (5) asserts
a supplement, not the different hyperplane assertion in B.5.6(5).

This publishes the target for lower Chapter B consumers. No field of the
conclusion is an input to the source theorem, and defining its universal
implication is not a proof of it.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1, pp.99–103.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
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

/-- The target universal B.5.1 implication. This is not an earlier-source input. -/
def QuasisimpleClassificationInput (K : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D]
    (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D),
    QuasisimpleSourceHypothesis ρ K L → Nonempty (QuasisimpleSourceConclusion ρ L)

end CFSG.Quasithin.ChapterB.QuasisimpleSource
