module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.ExceptionalSeven
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.SourceRemaining

/-!
# The natural permutation frontier for the original component

The exceptional A₇ four-space is excluded using the original moved seed
and the point stabilizer of order 168. The same selected component and
full B.5.1 moved section therefore retain only the natural symmetric-five
and symmetric-seven actions, or the previously isolated cubic A₆ cover.
All surviving action, offender and extension clauses remain literal.
No universal MS classification is used.

Source: Aschbacher--Smith original 15.2.23, printed pp.1116--1117,
and C.2.7, pp.145--147; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding TerminalLinear ChapterD ChapterD.UniqueFactor
open Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
universe u v w
section Actions
variable {D : Type v} [Group D] {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)

/-- The surviving finite-model B.4.2 actions, with no added Sylow bound.
Every surviving marked action and offender clause is retained. -/
inductive RemainingNaturalIrreducibleCase (L H : Subgroup D) : Prop
  | symmetric (n : ℕ) (degree : n = 5 ∨ n = 7)
      (e : MarkedActionEquiv ρ H L (BinaryPermutation.naturalRepresentation (Fin n))
        (alternatingGroup (Fin n)))
      (offenders : ∀ A, IsBestOffender ρ A →
        ChapterB.Offenders.CaseAFamily n
          ((A.subgroupOf H).map e.action.groupEquiv.toMonoidHom))
      (ratio : quadraticRatio ρ = 1)

/-- The natural symmetric-five/seven rows with all original moved-section clauses. -/
inductive RemainingNaturalActionCase (L : Subgroup D) (s : MovedSection ρ L) : Prop
  | irreducible (irrPlus : IsIrrPlus ρ L s.space.toSubmodule)
      (faithful : Function.Injective s.action)
      (irreducible : IsIrreducible (s.action.comp L.subtype))
      (source : RemainingNaturalIrreducibleCase s.action L (offenderSubgroup s.action))
      (extension : L = ⊤ ∨ (∀ T : Sylow 2 D, L ⊔ (T : Subgroup D) = ⊤) ∧
        OuterNaturalAction s.action)
end Actions

variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Removing the exceptional four-space preserves the original moved section. -/
theorem normalized_component_natural_action
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hCJ : starImage X ((M ⊓ I).pCoreIn 2) X ≤
      offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (hc : RemainingPermutationActionCase
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) c.sectionData) :
    RemainingNaturalActionCase
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) c.sectionData := by
  cases hc with
  | irreducible hp hf hi hr he =>
    apply RemainingNaturalActionCase.irreducible hp hf hi ?_ he
    cases hr with
    | symmetric n hn a ho hr => exact .symmetric n hn a ho hr
    | alternatingSeven _ _ a hd _ _ =>
      exact (normalized_exceptionalSeven_false d horbit hI hfit hcore selection
        hCJ c.sectionData hf a hd).elim

/-- The same original source component has a natural permutation action or
an A₆ star image with cubic center in its full core quotient. -/
theorem exists_source_natural_or_cubicSix_component
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (hi : OmegaAction.PlaneInverter hsource ZS) :
    ∃ X : Subgroup G, Normalized H M I X ∧
      let R := (M ⊓ I).pCoreIn 2
      let ρ := starRepresentation X R
      let J := offenderSubgroup ρ
      starImage X R X ≤ J ∧
        ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
            (ρ.comp J.subtype) ((starImage X R X).subgroupOf J),
          (RemainingNaturalActionCase (ρ.comp J.subtype) ((starImage X R X).subgroupOf J) c.sectionData ∨
            (Nonempty (starImage X R X ≃* alternatingGroup (Fin 6)) ∧
              Nat.card (center (X ⧸ pCore 2 X)) = 3)) := by
  obtain ⟨X,selection,hCJ,c,_,hc⟩ := exists_source_component_frontier
    d hquotient horbit hI hfit hno hNI ha hi
  let := hsource.prepared.elementary
  have ho := OmegaAction.omega_of_restricted_actions d hI ha hNI
  obtain ⟨eNI⟩ := OmegaAction.intersection_image_equiv_of_omega d hI hNI ho hi
  obtain ⟨f,hf,hker⟩ := OmegaAction.exists_symmetricThree_action_of_image_equiv eNI
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  refine ⟨X,selection,hCJ,c,?_⟩
  rcases hc with hc | hc
  · exact .inl (normalized_component_natural_action d horbit hI hfit hcore selection hCJ c hc)
  · exact .inr hc

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
