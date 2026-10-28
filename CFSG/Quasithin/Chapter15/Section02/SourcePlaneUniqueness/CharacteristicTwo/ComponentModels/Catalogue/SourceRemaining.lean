module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.ModelOnly.Source
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RemainingPermutation

/-!
# The original component reduction without universal MS module classification

The natural and doubled linear-three rows are excluded using their actual
full core models, the original NI action, plane inverter and Kc orbit.
The binary terminal, symplectic, G₂ and triple-six exclusions retain the
same selected component and moved section.

The result preserves the unresolved A₆ possibility: its full core quotient
has center of order three. Its previous exclusion used the rank-two field
of EarlierMSClassifications. The universal linear-three field of that record
is refuted by OriginalSource/MS/F4Obstruction, so that record cannot be an
input to unconditional source assembly. The legacy conditional APIs remain
unchanged. No MS classification premise is used in this module.

Source: Aschbacher--Smith original 15.2.23, pp.1116--1117, C.2.7,
pp.145--147, and B.5.1, pp.99--103; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding TerminalLinear ChapterD ChapterD.UniqueFactor
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The linear exclusions use only the original full core models and source
premises. The selected component and full moved-section conclusion are retained. -/
theorem normalized_component_remaining_action_of_core_models
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (selection : Normalized H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (hi : OmegaAction.PlaneInverter hsource ZS) :
    let R := (M ⊓ I).pCoreIn 2
    let ρ := starRepresentation X R
    let J := offenderSubgroup ρ
    starImage X R X ≤ J ∧
      ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
          (ρ.comp J.subtype) ((starImage X R X).subgroupOf J),
        RemainingActionCase (ρ.comp J.subtype) ((starImage X R X).subgroupOf J) c.sectionData := by
  let := hsource.prepared.elementary
  have ho := OmegaAction.omega_of_restricted_actions d hI ha hNI
  obtain ⟨eNI⟩ := OmegaAction.intersection_image_equiv_of_omega d hI hNI ho hi
  obtain ⟨f,hf,hker⟩ := OmegaAction.exists_symmetricThree_action_of_image_equiv eNI
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  have h := normalized_component_input (hsource := hsource) hI hcore selection
  obtain ⟨hCJ,⟨c⟩⟩ := star_moved_section_from_source h
  refine ⟨hCJ,c,?_⟩
  let e := (subgroupOfEquivOfLe hCJ).symm
  have hbin : ∀ n, n = 4 ∨ n = 5 →
      (starImage X ((M ⊓ I).pCoreIn 2) X ≃* SL(n,ZMod 2)) → False := by
    intro n hn a
    exact normalized_binary_false_from_preceding d hquotient horbit hI hfit
      selection hno hn a hNI ha hi
  let a8 : alternatingGroup (Fin 8) ≃* SL(4,ZMod 2) :=
    (Atlas.Order20160A8.sl4TwoEquivPSL.trans
      Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm).symm
  cases c.clause_one with
  | irreducible hp hf hirr hr hext =>
    apply RemainingActionCase.irreducible hp hf hirr ?_ hext
    cases hr with
    | linearTwo F _ a ho hr =>
      have hsy := (rankOne_row_geometry_from_source h hCJ c.sectionData F a hr ho).2.2
      exact (selection.toSelected.not_chi hno (source_chiZero_of_sylow_input h hsy).2.chi).elim
    | linearThree F _ a _ =>
      exact (normalized_component_naturalThree_false_of_core_model d horbit
        hI hfit selection hno hCJ c.sectionData F a hext hNI ha hi).elim
    | symplectic F hn hg a hr => exact .symplectic F hn hg a hr
    | symplecticTwo a hr => exact .symplecticTwo a hr
    | g2 F hn hg a ho hr => exact .g2 F hn hg a ho hr
    | g2Two a ho hr => exact .g2Two a ho hr
    | symmetric n hn a ho hr => exact .symmetric n hn a ho hr
    | alternatingSix hg a ho hr => exact .alternatingSix hg a ho hr
    | alternatingSeven hg ht a hd ho hr => exact .alternatingSeven hg ht a hd ho hr
    | tripleSix hg a hr => exact .tripleSix hg a hr
    | binaryLinear n hn _ a _ => exact (hbin n hn (e.trans a.groupEquiv)).elim
    | orthogonalSix _ _ a _ _ => exact (hbin 4 (Or.inl rfl) ((e.trans a.groupEquiv).trans a8)).elim
    | symmetricEight _ a _ => exact (hbin 4 (Or.inl rfl) ((e.trans a.subgroupEquiv).trans a8)).elim
    | exteriorFive _ _ a _ _ _ => exact (hbin 5 (Or.inr rfl) (e.trans a)).elim
  | doubleThree F ht a _ _ =>
    exact (normalized_component_doubleThree_false_of_core_model d horbit
      hI hfit selection hno hCJ c.sectionData F ht a hNI ha hi).elim
  | naturalDual n hn _ ha =>
    obtain ⟨a⟩ := ha
    exact (hbin n hn (e.trans a.groupEquiv)).elim
  | repeatedNatural n _ hn _ _ _ ha =>
    obtain ⟨a⟩ := ha
    exact (hbin n hn (e.trans a.groupEquiv)).elim


/-- Without MS reconstruction, the only extra row is the actual A₆ star
image with a cubic center in the full core quotient. -/
theorem normalized_component_permutation_or_cubicSix
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
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
    (hc : RemainingExceptionalActionCase
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) c.sectionData) :
    RemainingPermutationActionCase
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) c.sectionData ∨
      (Nonempty (starImage X ((M ⊓ I).pCoreIn 2) X ≃* alternatingGroup (Fin 6)) ∧
        Nat.card (center (X ⧸ pCore 2 X)) = 3) := by
  cases hc with
  | irreducible hp hf hi hr he =>
    cases hr with
    | symplecticTwo a _ =>
      let e := ((subgroupOfEquivOfLe hCJ).symm.trans a.subgroupEquiv).trans
        (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
          (F := ZMod 2) (by simp))
      exact .inr ⟨⟨e⟩,normalized_alternatingSix_core_center_three d horbit hI hcore selection e⟩
    | g2 F hn _ a _ _ =>
      exact (normalized_component_g2_false d hI hcore selection hn F.card_eq
        ((subgroupOfEquivOfLe hCJ).symm.trans a.groupEquiv)).elim
    | g2Two a _ _ =>
      exact (normalized_binaryG2_false d horbit hI hcore selection
        ((subgroupOfEquivOfLe hCJ).symm.trans a.subgroupEquiv)).elim
    | symmetric n hn a ho hr =>
      exact .inl (.irreducible hp hf hi (.symmetric n hn a ho hr) he)
    | alternatingSix _ a _ _ =>
      let e := (subgroupOfEquivOfLe hCJ).symm.trans a.groupEquiv
      exact .inr ⟨⟨e⟩,normalized_alternatingSix_core_center_three d horbit hI hcore selection e⟩
    | alternatingSeven hg ht a hd ho hr =>
      exact .inl (.irreducible hp hf hi (.alternatingSeven hg ht a hd ho hr) he)
    | tripleSix hg a hr =>
      exact (normalized_component_tripleSix_false d hI hcore selection hCJ c.sectionData hg a hr).elim

/-- The original source supplies the same normalized escaping component and
full moved section, with no universal MS classification parameter. The cubic
A₆ reconstruction and surviving permutation exclusions remain explicit rows. -/
theorem exists_source_component_frontier
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
          RemainingExceptionalActionCase (ρ.comp J.subtype) ((starImage X R X).subgroupOf J) c.sectionData ∧
          (RemainingPermutationActionCase (ρ.comp J.subtype) ((starImage X R X).subgroupOf J) c.sectionData ∨
            (Nonempty (starImage X R X ≃* alternatingGroup (Fin 6)) ∧
              Nat.card (center (X ⧸ pCore 2 X)) = 3)) := by
  obtain ⟨X,selection⟩ := OmegaAction.escaping_normalized_component_of_restricted_actions
    d hI hfit ha hi hNI hno
  obtain ⟨hCJ,c,hc⟩ := normalized_component_remaining_action_of_core_models
    d hquotient horbit hI hfit selection hno hNI ha hi
  let := hsource.prepared.elementary
  have ho := OmegaAction.omega_of_restricted_actions d hI ha hNI
  obtain ⟨eNI⟩ := OmegaAction.intersection_image_equiv_of_omega d hI hNI ho hi
  obtain ⟨f,hf,hker⟩ := OmegaAction.exists_symmetricThree_action_of_image_equiv eNI
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  have he := normalized_component_exceptional_action d hI hcore selection hCJ c hc
  exact ⟨X,selection,hCJ,c,he,
    normalized_component_permutation_or_cubicSix d horbit hI hcore selection hCJ c he⟩

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
