module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.LinearThreeSource
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Source

/-!
# The remaining original moved-section cases after all linear exclusions

The actual unrestricted B.5.1 section is retained on the selected escaping
component. Natural rank one is excluded by the full-Sylow block theorem;
the marked natural and doubled SL3 rows are excluded after the degree-one
reduction and the existing small MS classification. The completed terminal
owner excludes every binary L4/L5 row, without an assumed KS quotient.

The remaining irreducible actions retain their actual markings, offender,
ratio and extension clauses, together with the entire original B.5.1
conclusion. Their non-chi catalogue and original KS placement still require
proof. This reduction does not assert the completion of 15.2.23.

Source: Aschbacher--Smith B.5.1, pp.99--103, C.2.7, pp.145--147,
and original 15.2.23, pp.1116--1117; refs/quasithin.pdf.
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

/-- The remaining irreducible rows with the actual B.4.2 action and offender clauses.
Natural rank one, linear-three, and binary degree-four/five rows have been removed. -/
inductive RemainingIrreducibleCase (L H : Subgroup D) : Prop
  | symplectic (F : BinaryField) (large : 1 < F.degree) (generated : H = L)
      (e : ActionEquiv (ρ.comp L.subtype) (binarySymplectic F))
      (ratio : quadraticRatio ρ = 2 / 3)
  | symplecticTwo
      (e : MarkedActionEquiv ρ H L (symplecticNatural (k := ZMod 2) 2)
        (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))))
      (ratio : quadraticRatio ρ = 2 / 3)
  | g2 (F : BinaryField) (large : 1 < F.degree) (generated : H = L)
      (e : ActionEquiv (ρ.comp L.subtype) (binaryG2 F))
      (offenders : ∀ A, IsBestOffender ρ A → rank A = 3 * F.degree)
      (ratio : quadraticRatio ρ = 1)
  | g2Two (e : MarkedActionEquiv ρ H L (g2Natural (ZMod 2))
        (commutator (Atlas.G2.Model (ZMod 2))))
      (offenders : ∀ A, IsBestOffender ρ A → rank A = 3)
      (ratio : quadraticRatio ρ = 1)
  | symmetric (n : ℕ) (degree : n = 5 ∨ n = 7)
      (e : MarkedActionEquiv ρ H L (BinaryPermutation.naturalRepresentation (Fin n))
        (alternatingGroup (Fin n)))
      (offenders : ∀ A, IsBestOffender ρ A →
        ChapterB.Offenders.CaseAFamily n
          ((A.subgroupOf H).map e.action.groupEquiv.toMonoidHom))
      (ratio : quadraticRatio ρ = 1)
  | alternatingSix (generated : H = L)
      (e : ActionEquiv (ρ.comp L.subtype) (alternatingNatural 6))
      (offenders : ∀ A, IsBestOffender ρ A → rank A = 2 ∧
        ∃ g : alternatingGroup (Fin 6),
          ((A.subgroupOf L).map
            ((alternatingGroup (Fin 6)).subtype.comp e.groupEquiv.toMonoidHom)) =
          (ChapterB.Offenders.evenPart 6).map (MulAut.conj (g : Equiv.Perm (Fin 6))).toMonoidHom)
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
  | tripleSix (generated : H = L) (action : ChapterB.SourceInduction.ProjectiveLine.TripleSixAction ρ L)
      (ratio : quadraticRatio ρ = 1)

/-- The actual moved-section alternatives remaining after the block and binary exclusions. -/
inductive RemainingActionCase (L : Subgroup D) (s : MovedSection ρ L) : Prop
  | irreducible (irrPlus : IsIrrPlus ρ L s.space.toSubmodule)
      (faithful : Function.Injective s.action)
      (irreducible : IsIrreducible (s.action.comp L.subtype))
      (source : RemainingIrreducibleCase s.action L (offenderSubgroup s.action))
      (extension : L = ⊤ ∨ (∀ T : Sylow 2 D, L ⊔ (T : Subgroup D) = ⊤) ∧
        OuterNaturalAction s.action)
end Actions


variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- All linear rows are excluded on the same selected component. The full
original moved-section conclusion is retained alongside the remaining actions. -/
theorem normalized_component_remaining_action
    (hC134 : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
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
      exact (normalized_component_naturalThree_false_from_preceding d hC134 horbit
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
    exact (normalized_component_doubleThree_false_from_preceding d hC134 horbit
      hI hfit selection hno hCJ c.sectionData F ht a hNI ha hi).elim
  | naturalDual n hn _ ha =>
    obtain ⟨a⟩ := ha
    exact (hbin n hn (e.trans a.groupEquiv)).elim
  | repeatedNatural n _ hn _ _ _ ha =>
    obtain ⟨a⟩ := ha
    exact (hbin n hn (e.trans a.groupEquiv)).elim

/-- The original escaping I supplies a component with only the remaining
nonlinear source actions. No KS pair quotient is assumed. -/
theorem exists_remaining_component
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
          RemainingActionCase (ρ.comp J.subtype) ((starImage X R X).subgroupOf J) c.sectionData := by
  obtain ⟨X,s⟩ := OmegaAction.escaping_normalized_component_of_restricted_actions
    d hI hfit ha hi hNI hno
  exact ⟨X,s,normalized_component_remaining_action d hC134 hquotient horbit hI hfit
    s hno hNI ha hi⟩


end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
