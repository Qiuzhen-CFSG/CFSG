module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.TripleSix
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RemainingAlternating

/-!
# The permutation actions remaining in the original component

The actual ratio-one triple-six action places the Thompson image inside
the same component. Its cubic center lies in the original marked NI
intersection, contradicting the original rank-two residual. This removes
the triple-six row while retaining the selected X, original R and NI,
and the full moved section and surviving action clauses.

The symmetric-five/seven and exceptional A₇ rows remain, along with full
original KS placement and source assembly. The earlier small MS
classification retains its original producer.

Source: Aschbacher--Smith original 15.2.23, pp.1116--1117, and C.2.7,
pp.145--147; refs/quasithin.pdf.
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
inductive RemainingPermutationIrreducibleCase (L H : Subgroup D) : Prop
  | symmetric (n : ℕ) (degree : n = 5 ∨ n = 7)
      (e : MarkedActionEquiv ρ H L (BinaryPermutation.naturalRepresentation (Fin n))
        (alternatingGroup (Fin n)))
      (offenders : ∀ A, IsBestOffender ρ A →
        ChapterB.Offenders.CaseAFamily n
          ((A.subgroupOf H).map e.action.groupEquiv.toMonoidHom))
      (ratio : quadraticRatio ρ = 1)
  | alternatingSeven (generated : H = L) (whole : L = ⊤)
      (e : L ≃* alternatingGroup (Fin 7)) (dimension : Module.finrank (ZMod 2) W = 4)
      (offenders : ∀ A, IsBestOffender ρ A →
        ∃ g : alternatingGroup (Fin 7),
          ((A.subgroupOf L).map ((alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom)) =
          (Subgroup.closure {ChapterB.Offenders.kleinFirst 7 (by decide),
            ChapterB.Offenders.kleinSecond 7 (by decide)}).map
              (MulAut.conj (g : Equiv.Perm (Fin 7))).toMonoidHom)
      (ratio : quadraticRatio ρ = 1)


/-- The actual moved-section alternatives remaining after all linear, symplectic, G₂, A₆ and triple-six exclusions. -/
inductive RemainingPermutationActionCase (L : Subgroup D) (s : MovedSection ρ L) : Prop
  | irreducible (irrPlus : IsIrrPlus ρ L s.space.toSubmodule)
      (faithful : Function.Injective s.action)
      (irreducible : IsIrreducible (s.action.comp L.subtype))
      (source : RemainingPermutationIrreducibleCase s.action L (offenderSubgroup s.action))
      (extension : L = ⊤ ∨ (∀ T : Sylow 2 D, L ⊔ (T : Subgroup D) = ⊤) ∧
        OuterNaturalAction s.action)
end Actions


variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Removing triple-six preserves the same original moved section. -/
theorem normalized_component_permutation_action
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hCJ : starImage X ((M ⊓ I).pCoreIn 2) X ≤
      offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (hc : RemainingAlternatingActionCase
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) c.sectionData) :
    RemainingPermutationActionCase
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) c.sectionData := by
  cases hc with
  | irreducible hp hf hi hr he =>
    apply RemainingPermutationActionCase.irreducible hp hf hi ?_ he
    cases hr with
    | symmetric n hn a ho hr => exact .symmetric n hn a ho hr
    | alternatingSeven hg ht a hd ho hr => exact .alternatingSeven hg ht a hd ho hr
    | tripleSix hg a hr =>
      exact (normalized_component_tripleSix_false d hI hcore selection hCJ c.sectionData hg a hr).elim

/-- The original escaping I supplies a component with only the remaining
nonlinear source actions. No KS pair quotient is assumed. -/
theorem exists_remaining_permutation_component
    (hC134 : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
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
          RemainingPermutationActionCase (ρ.comp J.subtype) ((starImage X R X).subgroupOf J) c.sectionData := by
  obtain ⟨X,s,hCJ,c,hc⟩ := exists_remaining_alternating_component d hC134 hquotient horbit hI hfit hno hNI ha hi
  let := hsource.prepared.elementary
  have ho := OmegaAction.omega_of_restricted_actions d hI ha hNI
  obtain ⟨eNI⟩ := OmegaAction.intersection_image_equiv_of_omega d hI hNI ho hi
  obtain ⟨f,hf,hker⟩ := OmegaAction.exists_symmetricThree_action_of_image_equiv eNI
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  exact ⟨X,s,hCJ,c,normalized_component_permutation_action d hI hcore s hCJ c hc⟩

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
