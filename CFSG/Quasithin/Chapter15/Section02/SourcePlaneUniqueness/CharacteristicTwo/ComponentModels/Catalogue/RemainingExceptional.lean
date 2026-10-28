module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.Symplectic
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.Remaining

/-!
# The remaining exceptional actions on the original component

The nonbinary symplectic row, including every even field degree, is excluded
using the actual full-core parabolic and the solvable original H intersection.
This refines the existing linear exclusions on the same selected X and the
same B.5.1 moved section, retaining all offender, ratio and extension clauses.
The Omega action supplies the core equality required by the exclusion.

The binary symplectic, G2 and alternating rows remain. Their exclusions and
full original KS placement are still required for 15.2.23. The small C.1.34
classification keeps its earlier producer and final Theorem E discharge.

Source: Aschbacher--Smith original 15.2.23, pp.1116--1117;
refs/quasithin.pdf.
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
The nonbinary symplectic rows are also removed; all remaining action clauses are retained. -/
inductive RemainingExceptionalIrreducibleCase (L H : Subgroup D) : Prop
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

/-- The actual moved-section alternatives remaining after the linear and nonbinary symplectic exclusions. -/
inductive RemainingExceptionalActionCase (L : Subgroup D) (s : MovedSection ρ L) : Prop
  | irreducible (irrPlus : IsIrrPlus ρ L s.space.toSubmodule)
      (faithful : Function.Injective s.action)
      (irreducible : IsIrreducible (s.action.comp L.subtype))
      (source : RemainingExceptionalIrreducibleCase s.action L (offenderSubgroup s.action))
      (extension : L = ⊤ ∨ (∀ T : Sylow 2 D, L ⊔ (T : Subgroup D) = ⊤) ∧
        OuterNaturalAction s.action)
end Actions


variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Removing the nonbinary symplectic row keeps the same original moved section. -/
theorem normalized_component_exceptional_action
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
    (hc : RemainingActionCase
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) c.sectionData) :
    RemainingExceptionalActionCase
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) c.sectionData := by
  cases hc with
  | irreducible hp hf hi hr he =>
    apply RemainingExceptionalActionCase.irreducible hp hf hi ?_ he
    cases hr with
    | symplectic F hn _ a _ =>
      exact (normalized_component_symplectic_false d hI hcore selection hn F.card_eq
        ((subgroupOfEquivOfLe hCJ).symm.trans a.groupEquiv)).elim
    | symplecticTwo a hr => exact .symplecticTwo a hr
    | g2 F hn hg a ho hr => exact .g2 F hn hg a ho hr
    | g2Two a ho hr => exact .g2Two a ho hr
    | symmetric n hn a ho hr => exact .symmetric n hn a ho hr
    | alternatingSix hg a ho hr => exact .alternatingSix hg a ho hr
    | alternatingSeven hg ht a hd ho hr => exact .alternatingSeven hg ht a hd ho hr
    | tripleSix hg a hr => exact .tripleSix hg a hr

/-- The original escaping I supplies a component with only the remaining
nonlinear source actions. No KS pair quotient is assumed. -/
theorem exists_remaining_exceptional_component
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
          RemainingExceptionalActionCase (ρ.comp J.subtype) ((starImage X R X).subgroupOf J) c.sectionData := by
  obtain ⟨X,s,hCJ,c,hc⟩ := exists_remaining_component d hC134 hquotient horbit hI hfit hno hNI ha hi
  let := hsource.prepared.elementary
  have ho := OmegaAction.omega_of_restricted_actions d hI ha hNI
  obtain ⟨eNI⟩ := OmegaAction.intersection_image_equiv_of_omega d hI hNI ho hi
  obtain ⟨f,hf,hker⟩ := OmegaAction.exists_symmetricThree_action_of_image_equiv eNI
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  exact ⟨X,s,hCJ,c,normalized_component_exceptional_action d hI hcore s hCJ c hc⟩

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
