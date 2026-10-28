module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.Blocks
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.ComponentSelection
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.LinearBinary
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.NonlinearNonbinary
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.SevenExclusion
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.SevenExceptional
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.LinearThreeMarking

/-!
# Reduction of the actual equality-row component to a linear-three parabolic

Apply the proved C.2.7 source extraction to the original normalized component
and its literal radical O₂(M intersect I). Every binary-linear, symplectic,
G₂, alternating and triple-six action is excluded on the same component.
The two remaining B.5 actions provide the actual marked linear-three
parabolic, with a finite binary field retained. The source consumer constructs
the component and discharges no-chi and NI escape from the original equality
row. The remaining linear-three contradiction is consumed by Source.

Source: Aschbacher--Smith 15.2.23, pp.1116--1117; C.2.7, pp.145--147;
B.5.1, pp.99--103, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 PlaneUniquenessPreceding TerminalLinear ComponentCatalogue
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (r : ResidualInput hsource H B)
include r

/-- The full B.5 source action on the original component leaves a marked
linear-three parabolic, retaining its actual finite binary field. -/
theorem ResidualInput.normalized_linearThree_parabolic_of_eq
    (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y) :
    ∃ F : BinaryField, IsLinearMaximalParabolic
      ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
        (starImage X ((M ⊓ I).pCoreIn 2) X)) 3 F.Carrier := by
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  obtain ⟨hCJ,⟨c⟩⟩ := star_moved_section_from_source h
  let e := (subgroupOfEquivOfLe hCJ).symm
  have hbin : ∀ n, n = 4 ∨ n = 5 →
      (starImage X ((M ⊓ I).pCoreIn 2) X ≃* SL(n,ZMod 2)) → False := by
    intro n hn a
    exact r.normalized_binary_false_of_eq he hI hfit hcore selection hno hn a
  let a8 : alternatingGroup (Fin 8) ≃* SL(4,ZMod 2) :=
    (Atlas.Order20160A8.sl4TwoEquivPSL.trans
      Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm).symm
  cases c.clause_one with
  | irreducible hp hf hirr hr hext =>
    cases hr with
    | linearTwo F _ a ho hr =>
      have hsy := (rankOne_row_geometry_from_source h hCJ c.sectionData F a hr ho).2.2
      exact (selection.toSelected.not_chi hno (source_chiZero_of_sylow_input h hsy).2.chi).elim
    | linearThree F _ a _ =>
      obtain ⟨_,hpar⟩ | ⟨_,hpar⟩ := normalized_component_naturalThree_parabolic
        (hsource := hsource) hI hcore selection hno hCJ c.sectionData F a hext
      · exact ⟨BinaryField.two,hpar⟩
      · exact ⟨F,hpar⟩
    | symplectic F hn _ a _ =>
      exact (r.normalized_component_symplectic_false hI hcore selection hn F.card_eq
        (e.trans a.groupEquiv)).elim
    | symplecticTwo a _ =>
      exact (r.normalized_alternatingSix_false_of_eq he hI hfit hcore hno selection
        ((e.trans a.subgroupEquiv).trans
          (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
            (F := ZMod 2) (by simp)))).elim
    | g2 F hn _ a _ _ =>
      exact (r.normalized_component_g2_false hI hcore selection hn F.card_eq
        (e.trans a.groupEquiv)).elim
    | g2Two a _ _ =>
      exact (r.binaryG2_false_of_eq he hI hcore selection (e.trans a.subgroupEquiv)).elim
    | symmetric n hn a _ hr =>
      exact (r.normalized_symmetric_false_of_eq he hI hfit hcore selection hno hCJ
        c.sectionData hp hn a hr).elim
    | alternatingSix _ a _ _ =>
      exact (r.normalized_alternatingSix_false_of_eq he hI hfit hcore hno selection
        (e.trans a.groupEquiv)).elim
    | alternatingSeven _ _ a hd _ _ =>
      exact (r.normalized_exceptionalSeven_false_of_eq he hI hfit hcore selection hCJ
        c.sectionData hf a hd).elim
    | tripleSix hg a hr =>
      exact (r.normalized_component_tripleSix_false hI hcore selection hCJ
        c.sectionData hg a hr).elim
    | binaryLinear n hn _ a _ => exact (hbin n hn (e.trans a.groupEquiv)).elim
    | orthogonalSix _ _ a _ _ =>
      exact (hbin 4 (Or.inl rfl) ((e.trans a.groupEquiv).trans a8)).elim
    | symmetricEight _ a _ =>
      exact (hbin 4 (Or.inl rfl) ((e.trans a.subgroupEquiv).trans a8)).elim
    | exteriorFive _ _ a _ _ _ => exact (hbin 5 (Or.inr rfl) (e.trans a)).elim
  | doubleThree F ht a _ _ =>
    obtain ⟨_,hpar⟩ | ⟨_,hpar⟩ := normalized_component_doubleThree_parabolic
      (hsource := hsource) hI hcore selection hno hCJ c.sectionData F ht a
    · exact ⟨BinaryField.two,hpar⟩
    · exact ⟨F,hpar⟩
  | naturalDual n hn _ ha =>
    obtain ⟨a⟩ := ha
    exact (hbin n hn (e.trans a.groupEquiv)).elim
  | repeatedNatural n _ hn _ _ _ ha =>
    obtain ⟨a⟩ := ha
    exact (hbin n hn (e.trans a.groupEquiv)).elim

/-- The original equality row and escaping I supply the same normalized
component with its literal linear-three parabolic. -/
theorem ResidualInput.characteristicTwo_linearThree_parabolic_of_eq
    (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I) :
    ∃ X : Subgroup G, Normalized H M I X ∧
      ∃ F : BinaryField, IsLinearMaximalParabolic
        ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
          (starImage X ((M ⊓ I).pCoreIn 2) X)) 3 F.Carrier := by
  have hno := r.no_chi_block_of_eq he hI hfit
  have hNI : ¬ M ⊓ I ≤ Mc ⊓ I :=
    r.characteristicTwo_false_of_intersection_le_of_eq he hI hfit
  have hcore := r.intersection_core_eq_of_not_le_partner hI hNI
  obtain ⟨X,selection⟩ := r.escaping_normalized_component_of_not_le_partner hI hfit hno hNI
  exact ⟨X,selection,r.normalized_linearThree_parabolic_of_eq he hI hfit hcore selection hno⟩

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
