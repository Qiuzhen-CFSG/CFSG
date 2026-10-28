module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RemainingMarked
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.AlternatingFive

/-!
# The seven-letter and cubic symplectic frontier

The original Sylow subgroup normalizes the two-radical image. In the
five-letter case that image contains a full alternating Sylow, forcing a
forbidden chi-zero block. Thus the remaining natural coordinates have
exactly seven letters. The same selected component, original star maps,
full B.5 moved section and every surviving action clause are retained.

The seven-letter block reconstruction, cubic symplectic exclusion, full
original KS placement and final 15.2.23 assembly remain open.

Source: Aschbacher--Smith original 15.2.23, pp.1116--1117, C.2.7,
pp.145--147, and B.5.1, pp.99--103.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding TerminalLinear ChapterD ChapterD.UniqueFactor
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
universe u
variable {G : Type u} [Group G] [Finite G] {X R : Subgroup G}

/-- Seven-letter coordinates retain the whole star quotient, its original
alternating component and the literal moved central quotient action. -/
def FullSevenPermutationCoordinates
    (s : MovedSection ((starRepresentation X R).comp
      (offenderSubgroup (starRepresentation X R)).subtype)
      ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R)))) : Prop :=
  ∃ e : StarQuotient X R ≃* Equiv.Perm (Fin 7),
    ∃ A : (s.space.toSubmodule ⧸ s.central.toSubmodule) ≃ₗ[ZMod 2]
      BinaryPermutation.natural (Fin 7),
      (starImage X R X).map e.toMonoidHom = alternatingGroup (Fin 7) ∧
      (∀ j : offenderSubgroup (starRepresentation X R),
        ∀ v : s.space.toSubmodule ⧸ s.central.toSubmodule,
        A (s.central.quotientRepresentation j v) =
          BinaryPermutation.naturalRepresentation (Fin 7) (e j) (A v))

variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The original no-chi hypothesis removes degree five from the full marked
natural coordinates. -/
theorem normalized_component_seven_coordinates
    (hI : PlaneEscapes Mc ZS I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (s : MovedSection ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
      (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (hc : FullNaturalPermutationCoordinates s) :
    FullSevenPermutationCoordinates s := by
  obtain ⟨n,hn,e,A,hmark,ha,_⟩ := hc
  rcases hn with rfl | rfl
  · exact (normalized_alternatingFive_false d hI hcore selection hno
      ((e.subgroupMap _).trans (MulEquiv.subgroupCongr hmark))).elim
  · exact ⟨e,A,hmark,ha⟩

/-- The same original component and full moved section have seven-letter
natural coordinates or the cubic binary-symplectic alternative. -/
theorem exists_source_seven_or_cubicSymplectic_component
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
          ((RemainingNaturalActionCase (ρ.comp J.subtype) ((starImage X R X).subgroupOf J) c.sectionData ∧
            FullSevenPermutationCoordinates c.sectionData) ∨
            (Nonempty (starImage X R X ≃* alternatingGroup (Fin 6)) ∧
              Nat.card (center (X ⧸ pCore 2 X)) = 3 ∧
              quadraticRatio c.sectionData.action = 2 / 3)) := by
  obtain ⟨X,selection,hCJ,c,hc⟩ := exists_source_marked_or_cubicSymplectic_component
    d hquotient horbit hI hfit hno hNI ha hi
  let := hsource.prepared.elementary
  have ho := OmegaAction.omega_of_restricted_actions d hI ha hNI
  obtain ⟨eNI⟩ := OmegaAction.intersection_image_equiv_of_omega d hI hNI ho hi
  obtain ⟨f,hf,hker⟩ := OmegaAction.exists_symmetricThree_action_of_image_equiv eNI
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  refine ⟨X,selection,hCJ,c,?_⟩
  rcases hc with ⟨hn,hcoords⟩ | hs
  · exact .inl ⟨hn,normalized_component_seven_coordinates d hI hcore selection hno _ hcoords⟩
  · exact .inr hs

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
