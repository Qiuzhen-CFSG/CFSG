module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.SourceContracts.Irreducible
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives
/-!
# Full FF contracts with the corrected triple-six projective line

These separately named B.5.1 and B.5.6 contracts propagate the K.1.3
vector-plane convention through every source clause. All unchanged module,
factor, extension and source-hypothesis contracts are reused. In particular
no new global classification premise stronger than the printed source is
introduced. The universal implications remain explicit inputs.

The group extraction and three-prime-core theorem reuse the established
model calculations. Neither depends on the triple-six offender clause.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.2(8),
p.86; B.5.1 and B.5.6, pp.99–110; K.1.3, p.453.
-/
@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

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

/-- The full universal B.5.1 implication; to be supplied by its theorem owner. -/
def QuasisimpleClassificationInput (K : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D]
    (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D),
    QuasisimpleSourceHypothesis ρ K L → Nonempty (QuasisimpleSourceConclusion ρ L)


/-- The source-complete classification conclusion, with the degenerate actor
allowed by the printed hypotheses. -/
inductive SourceAlternative : Prop
  | trivial (actor : Subsingleton D)
  | quasisimple (quasisimple : IsQuasisimple (generalizedFitting D))
      (actions : QuasisimpleSourceConclusion ρ (generalizedFitting D))
  | symmetricThree (case : SymmetricThreeCase ρ)
  | twoFactors (case : SourceTwoFactorCase ρ)
  | outerSixThree (case : OuterSixThreeCase ρ)
  | hyperplane (case : HyperplaneCase ρ)

/-- Group-case extraction from the full source alternatives. It contains no
core conclusion, and the quasisimple actor is the actual F*(D). -/
theorem SourceAlternative.groupCases (h : SourceAlternative ρ) :
    Subsingleton D ∨
      (IsQuasisimple (generalizedFitting D) ∧ QuasisimpleModel (generalizedFitting D)) ∨
      NonQuasisimpleAlternative ρ := by
  cases h with
  | trivial h => exact Or.inl h
  | quasisimple hq ha => exact Or.inr (Or.inl ⟨hq, ha.fittingModel ρ⟩)
  | symmetricThree h => exact Or.inr (Or.inr (.symmetricThree h))
  | twoFactors h => exact Or.inr (Or.inr (.twoFactors (h.toBasic ρ)))
  | outerSixThree h => exact Or.inr (Or.inr (.outerSixThree h))
  | hyperplane h => exact Or.inr (Or.inr (.hyperplane h))

/-- An FF witness removes only the trivial-actor case. -/
theorem SourceAlternative.groupCases_of_ff (h : SourceAlternative ρ) (hff : IsFFModule ρ) :
    (IsQuasisimple (generalizedFitting D) ∧ QuasisimpleModel (generalizedFitting D)) ∨
      NonQuasisimpleAlternative ρ := by
  rcases h.groupCases ρ with ht | h
  · let : Subsingleton D := ht
    let : Nontrivial D := nontrivial_of_ff ρ hff
    obtain ⟨g, hg⟩ := exists_ne (1 : D)
    exact (hg (Subsingleton.elim _ _)).elim
  · exact h

/-- Universal B.5.6 for the chosen K, with every B.5.3 hypothesis supplied
by `FFHypothesis`, including its genuine finite cover and quotient equivalence. -/
def GeneralClassificationInput (K : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D]
    (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V), FFHypothesis K ρ → SourceAlternative ρ

/-- Both complete universal implications; no additional model or core premise. -/
structure CompleteClassificationInput (K : GroupClass.{u}) : Prop where
  quasisimple : QuasisimpleClassificationInput.{u,v} K
  general : GeneralClassificationInput.{u,v} K

/-- The conditional group extraction used by the final assembly owner. -/
theorem CompleteClassificationInput.groupCases [Finite D] {K : GroupClass.{u}}
    (h : CompleteClassificationInput.{u,v} K) (hyp : FFHypothesis K ρ) :
    Subsingleton D ∨
      (IsQuasisimple (generalizedFitting D) ∧ QuasisimpleModel (generalizedFitting D)) ∨
      NonQuasisimpleAlternative ρ :=
  (h.general D V ρ hyp).groupCases ρ

/-- The nontrivial conditional extraction, using the consumer's actual FF witness. -/
theorem CompleteClassificationInput.groupCases_of_ff [Finite D] {K : GroupClass.{u}}
    (h : CompleteClassificationInput.{u,v} K) (hyp : FFHypothesis K ρ) (hff : IsFFModule ρ) :
    (IsQuasisimple (generalizedFitting D) ∧ QuasisimpleModel (generalizedFitting D)) ∨
      NonQuasisimpleAlternative ρ :=
  (h.general D V ρ hyp).groupCases_of_ff ρ hff


/-- The complete conditional FF classification eliminates the actor's
three-prime core. The FF witness removes the degenerate trivial-actor branch;
the remaining quasisimple and nonquasisimple alternatives are discharged by
their actual model and factor core calculations. -/
theorem CompleteClassificationInput.threePrimeCore_eq_bot
    [Finite D] {K : GroupClass.{u}}
    (h : CompleteClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) (hff : IsFFModule ρ) :
    pPrimeCore 3 D = ⊥ := by
  rcases h.groupCases_of_ff ρ hyp hff with ⟨hq, hm⟩ | hnq
  · exact threePrimeCore_eq_bot_of_quasisimple_alternative hm
      (fun _ => Theory.SpecificGroups.g2_derived_two_center_isThreeGroup)
  · exact hnq.threePrimeCore_eq_bot ρ hyp.generated hyp.twoCore

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine
