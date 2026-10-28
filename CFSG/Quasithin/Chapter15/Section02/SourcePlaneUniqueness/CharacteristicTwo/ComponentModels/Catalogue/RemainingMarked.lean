module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RemainingNatural
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.CubicSixThompson
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.NaturalPermutation

/-!
# The marked permutation and cubic symplectic frontier

The natural A₆ row is excluded by its inner Thompson action, independently
of MS classification. The same selected component and full B.5 moved
section retain the natural S₅/S₇ actions or the binary symplectic A₆
four-space with cubic core center and ratio two-thirds.

For each natural permutation row, the whole original star group is
identified with Sₙ. The equivalence maps the original component image
to Aₙ and intertwines the literal moved central quotient with the natural
module. In degree five the original component star map has kernel exactly
O₂(X). All original action and offender clauses remain available.

The natural block reconstruction, cubic symplectic exclusion, full KS
placement and final 15.2.23 assembly remain open. No universal MS premise
or stronger Sylow restriction is introduced.

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

/-- Full symmetric coordinates on the original star group and its literal
moved central quotient, with the original alternating component marking. -/
def FullNaturalPermutationCoordinates
    (s : MovedSection ((starRepresentation X R).comp
      (offenderSubgroup (starRepresentation X R)).subtype)
      ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R)))) : Prop :=
  ∃ n : ℕ, (n = 5 ∨ n = 7) ∧
    ∃ e : StarQuotient X R ≃* Equiv.Perm (Fin n),
      ∃ A : (s.space.toSubmodule ⧸ s.central.toSubmodule) ≃ₗ[ZMod 2]
        BinaryPermutation.natural (Fin n),
      (starImage X R X).map e.toMonoidHom = alternatingGroup (Fin n) ∧
      (∀ j : offenderSubgroup (starRepresentation X R),
        ∀ v : s.space.toSubmodule ⧸ s.central.toSubmodule,
        A (s.central.quotientRepresentation j v) =
          BinaryPermutation.naturalRepresentation (Fin n) (e j) (A v)) ∧
      (n = 5 → (toStarImage X R).ker = pCore 2 X)

variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

omit d in
include hsource in
/-- The remaining natural row gives full coordinates, not just an abstract
symmetric or alternating family identification. -/
theorem normalized_component_full_natural_coordinates
    (hI : PlaneEscapes Mc ZS I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hCJ : starImage X ((M ⊓ I).pCoreIn 2) X ≤
      offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))
    (s : MovedSection ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
      (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (hc : RemainingNaturalActionCase
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) s) :
    FullNaturalPermutationCoordinates s := by
  cases hc with
  | irreducible _ _ _ hr _ =>
    cases hr with
    | symmetric n hn a _ hr =>
      let h := normalized_component_input (hsource := hsource) hI hcore selection
      obtain ⟨e,he,ha⟩ := natural_permutation_star_coordinates h hCJ s hn a hr
      refine ⟨n,hn,e,a.action.linearEquiv,?_,ha,?_⟩
      · apply le_antisymm
        · rintro _ ⟨x,hx,rfl⟩
          change e x ∈ alternatingGroup (Fin n)
          rw [he ⟨x,hx⟩]
          exact (a.subgroupEquiv _).property
        · intro y hy
          let l := a.subgroupEquiv.symm ⟨y,hy⟩
          let x := subgroupOfEquivOfLe hCJ l
          refine ⟨x,x.property,?_⟩
          change e x = y
          rw [he x]
          change (a.subgroupEquiv ((subgroupOfEquivOfLe hCJ).symm
            (subgroupOfEquivOfLe hCJ (a.subgroupEquiv.symm ⟨y,hy⟩))) : Equiv.Perm (Fin n)) = y
          rw [MulEquiv.symm_apply_apply,MulEquiv.apply_symm_apply]
      · intro hfive
        subst n
        have hi := alternatingFive_coreToStar_injective h
          ((subgroupOfEquivOfLe hCJ).symm.trans a.subgroupEquiv)
        apply le_antisymm ?_ (core_le_toStarImage_ker selection.radical_normalizes)
        intro x hx
        apply (QuotientGroup.eq_one_iff (N := pCore 2 X) x).mp
        apply hi
        change coreToStar selection.radical_normalizes (QuotientGroup.mk' (pCore 2 X) x) =
          coreToStar selection.radical_normalizes 1
        rw [coreToStar_mk,map_one]
        exact hx


/-- The natural A₆ row is excluded without MS reconstruction. The only
cubic A₆ row left is the binary symplectic action of ratio two-thirds. -/
theorem normalized_component_natural_or_cubicSymplectic
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
    (hc : RemainingExceptionalActionCase
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) c.sectionData) :
    RemainingNaturalActionCase
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) c.sectionData ∨
      (Nonempty (starImage X ((M ⊓ I).pCoreIn 2) X ≃* alternatingGroup (Fin 6)) ∧
        Nat.card (center (X ⧸ pCore 2 X)) = 3 ∧
        quadraticRatio c.sectionData.action = 2 / 3) := by
  cases hc with
  | irreducible hp hf hi hr he =>
    cases hr with
    | symplecticTwo a hr =>
      let e := ((subgroupOfEquivOfLe hCJ).symm.trans a.subgroupEquiv).trans
        (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
          (F := ZMod 2) (by simp))
      exact .inr ⟨⟨e⟩,normalized_alternatingSix_core_center_three d horbit hI hcore selection e, hr⟩
    | g2 F hn _ a _ _ =>
      exact (normalized_component_g2_false d hI hcore selection hn F.card_eq
        ((subgroupOfEquivOfLe hCJ).symm.trans a.groupEquiv)).elim
    | g2Two a _ _ =>
      exact (normalized_binaryG2_false d horbit hI hcore selection
        ((subgroupOfEquivOfLe hCJ).symm.trans a.subgroupEquiv)).elim
    | symmetric n hn a ho hr =>
      exact .inl (.irreducible hp hf hi (.symmetric n hn a ho hr) he)
    | alternatingSix hg a _ hr =>
      exact (normalized_component_naturalSix_false d horbit hI hcore selection
        hCJ c.sectionData hg a hr).elim
    | alternatingSeven _ _ a hd _ _ =>
      exact (normalized_exceptionalSeven_false d horbit hI hfit hcore selection
        hCJ c.sectionData hf a hd).elim
    | tripleSix hg a hr =>
      exact (normalized_component_tripleSix_false d hI hcore selection hCJ c.sectionData hg a hr).elim

/-- The same source component retains the full B.5 moved section. The natural
rows have full marked symmetric coordinates; the only remaining cubic A₆
action has ratio two-thirds. No universal MS classification is assumed. -/
theorem exists_source_marked_or_cubicSymplectic_component
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
            FullNaturalPermutationCoordinates c.sectionData) ∨
            (Nonempty (starImage X R X ≃* alternatingGroup (Fin 6)) ∧
              Nat.card (center (X ⧸ pCore 2 X)) = 3 ∧
              quadraticRatio c.sectionData.action = 2 / 3)) := by
  obtain ⟨X,selection,hCJ,c,hc,_⟩ := exists_source_component_frontier
    d hquotient horbit hI hfit hno hNI ha hi
  let := hsource.prepared.elementary
  have ho := OmegaAction.omega_of_restricted_actions d hI ha hNI
  obtain ⟨eNI⟩ := OmegaAction.intersection_image_equiv_of_omega d hI hNI ho hi
  obtain ⟨f,hf,hker⟩ := OmegaAction.exists_symmetricThree_action_of_image_equiv eNI
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  refine ⟨X,selection,hCJ,c,?_⟩
  rcases normalized_component_natural_or_cubicSymplectic
    d horbit hI hfit hcore selection hCJ c hc with hn | hs
  · exact .inl ⟨hn,normalized_component_full_natural_coordinates (hsource := hsource) hI hcore selection hCJ _ hn⟩
  · exact .inr hs

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
