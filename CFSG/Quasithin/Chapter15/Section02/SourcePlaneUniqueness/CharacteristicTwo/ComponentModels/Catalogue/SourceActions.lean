module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.BinaryExclusion

/-!
# Remaining source actions after the rank-one and binary exclusions

On the same normalized escaping component X, the full B.5.1 moved-section
conclusion has no natural rank-one row: the actual offenders make R Sylow
in XR, which would make X a forbidden chi-zero block. The original binary
exclusion removes all L₄(2) and L₅(2) rows, including both alternating-eight
realizations, natural plus dual, repeated natural and exterior-five.

The surviving action cases retain the original moved section, field,
marked action, offenders, extension and ratio clauses. The complete B.5.1
conclusion is retained alongside them, including its central-extension
clauses. The binary contradiction is discharged on the original X, R and
NI; it is not a catalogue hypothesis.

This is a source-action reduction, not the exhaustive marked C.2.7 result.
The surviving linear-three rows still require their parabolic and MS
recognition; the other rows require the source-specific three-rank and
centralizer placement exclusions. Earlier source premises retain their
geometry, small-parabolic and block-exclusion producers and final discharge
at plane uniqueness.

Source: Aschbacher--Smith B.5.1, pp.99--103; C.2.7, pp.145--147; original
15.2.23, pp.1116--1117; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding TerminalLinear ChapterD ChapterD.UniqueFactor
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
universe u v w
section Actions
variable {D : Type v} [Group D] {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)

/-- The remaining irreducible rows with the actual B.4.2 action and offender clauses.
Natural rank one and all binary degree-four/five rows have been removed. -/
inductive NonterminalIrreducibleCase (L H : Subgroup D) : Prop
  | linearThree (F : BinaryField) (generated : H = L)
      (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F 3))
      (ratio : quadraticRatio ρ = 1 / 2)
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
inductive NonterminalActionCase (L : Subgroup D) (s : MovedSection ρ L) : Prop
  | irreducible (irrPlus : IsIrrPlus ρ L s.space.toSubmodule)
      (faithful : Function.Injective s.action)
      (irreducible : IsIrreducible (s.action.comp L.subtype))
      (source : NonterminalIrreducibleCase s.action L (offenderSubgroup s.action))
      (extension : L = ⊤ ∨ (∀ T : Sylow 2 D, L ⊔ (T : Subgroup D) = ⊤) ∧
        OuterNaturalAction s.action)
  | doubleThree (F : BinaryField) (whole : L = ⊤)
      (e : ActionEquiv (s.space.toRepresentation.comp L.subtype)
        (repeated (linearNatural F 3) 2))
      (offenders : ∀ A, IsBestOffender s.space.toRepresentation A ↔
        IsFullAxisGroup F 3 ((A.subgroupOf L).map e.groupEquiv.toMonoidHom))
      (ratio : quadraticRatio ρ = 1)
end Actions

variable {G : Type u} [Group G] [Finite G] {I X R N : Subgroup G}

private noncomputable def alternatingEightToBinary :
    alternatingGroup (Fin 8) ≃* SL(4,ZMod 2) :=
  (Atlas.Order20160A8.sl4TwoEquivPSL.trans
    Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm).symm

private theorem inspect_source_irreducible
    (h : Input KnownSimple.IsKnownSimple I R N X) (hno : ¬ ChapterC.IsChiBlock X)
    (hbin : ∀ n, n = 4 ∨ n = 5 → (starImage X R X ≃* SL(n,ZMod 2)) → False)
    (hCJ : starImage X R X ≤ offenderSubgroup (starRepresentation X R))
    (s : MovedSection ((starRepresentation X R).comp (offenderSubgroup (starRepresentation X R)).subtype)
      ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R))))
    (hs : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase s.action
      ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R)))
      (offenderSubgroup s.action)) :
    NonterminalIrreducibleCase s.action
      ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R)))
      (offenderSubgroup s.action) := by
  let e := (subgroupOfEquivOfLe hCJ).symm
  cases hs with
  | linearTwo F _ a ho hr =>
    have hsy := (rankOne_row_geometry_from_source h hCJ s F a hr ho).2.2
    exact (hno (source_chiZero_of_sylow_input h hsy).2.chi).elim
  | linearThree F hg a hr => exact .linearThree F hg a hr
  | symplectic F hn hg a hr => exact .symplectic F hn hg a hr
  | symplecticTwo a hr => exact .symplecticTwo a hr
  | g2 F hn hg a ho hr => exact .g2 F hn hg a ho hr
  | g2Two a ho hr => exact .g2Two a ho hr
  | symmetric n hn a ho hr => exact .symmetric n hn a ho hr
  | alternatingSix hg a ho hr => exact .alternatingSix hg a ho hr
  | alternatingSeven hg ht a hd ho hr => exact .alternatingSeven hg ht a hd ho hr
  | tripleSix hg a hr => exact .tripleSix hg a hr
  | binaryLinear n hn _ a _ => exact (hbin n hn (e.trans a.groupEquiv)).elim
  | orthogonalSix _ _ a _ _ =>
    exact (hbin 4 (Or.inl rfl) ((e.trans a.groupEquiv).trans alternatingEightToBinary)).elim
  | symmetricEight _ a _ =>
    exact (hbin 4 (Or.inl rfl) ((e.trans a.subgroupEquiv).trans alternatingEightToBinary)).elim
  | exteriorFive _ _ a _ _ _ => exact (hbin 5 (Or.inr rfl) (e.trans a)).elim

private theorem inspect_source_action
    (h : Input KnownSimple.IsKnownSimple I R N X) (hno : ¬ ChapterC.IsChiBlock X)
    (hbin : ∀ n, n = 4 ∨ n = 5 → (starImage X R X ≃* SL(n,ZMod 2)) → False)
    (hCJ : starImage X R X ≤ offenderSubgroup (starRepresentation X R))
    (s : MovedSection ((starRepresentation X R).comp (offenderSubgroup (starRepresentation X R)).subtype)
      ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R))))
    (hs : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleActionCase
      ((starRepresentation X R).comp (offenderSubgroup (starRepresentation X R)).subtype)
      ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R))) s) :
    NonterminalActionCase
      ((starRepresentation X R).comp (offenderSubgroup (starRepresentation X R)).subtype)
      ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R))) s := by
  let e := (subgroupOfEquivOfLe hCJ).symm
  cases hs with
  | irreducible hp hf hi hr he =>
    exact .irreducible hp hf hi (inspect_source_irreducible h hno hbin hCJ s hr) he
  | doubleThree F ht a ho hr => exact .doubleThree F ht a ho hr
  | naturalDual n hn _ ha =>
    obtain ⟨a⟩ := ha
    exact (hbin n hn (e.trans a.groupEquiv)).elim
  | repeatedNatural n r hn _ _ _ ha =>
    obtain ⟨a⟩ := ha
    exact (hbin n hn (e.trans a.groupEquiv)).elim

variable {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Inspect the full B.5.1 conclusion on the same original normalized component.
All binary and natural rank-one contradictions are discharged internally. -/
theorem normalized_component_nonterminal_action
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (s : Normalized H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
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
        NonterminalActionCase (ρ.comp J.subtype) ((starImage X R X).subgroupOf J) c.sectionData := by
  let := hsource.prepared.elementary
  have ho := OmegaAction.omega_of_restricted_actions d hI ha hNI
  obtain ⟨eNI⟩ := OmegaAction.intersection_image_equiv_of_omega d hI hNI ho hi
  obtain ⟨f,hf,hker⟩ := OmegaAction.exists_symmetricThree_action_of_image_equiv eNI
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  have h := normalized_component_input (hsource := hsource) hI hcore s
  obtain ⟨hCJ,⟨c⟩⟩ := star_moved_section_from_source h
  refine ⟨hCJ,c,inspect_source_action h (s.toSelected.not_chi hno) ?_ hCJ _ c.clause_one⟩
  intro n hn e
  exact normalized_binary_false d hquotient horbit hI hfit s hno hn e hpair hNI ha hi

/-- The original escaping I supplies a normalized component and its surviving
full moved-section action; no component-selection or binary callback remains. -/
theorem exists_nonterminal_component
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
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
          NonterminalActionCase (ρ.comp J.subtype) ((starImage X R X).subgroupOf J) c.sectionData := by
  obtain ⟨X,s⟩ := OmegaAction.escaping_normalized_component_of_restricted_actions
    d hI hfit ha hi hNI hno
  exact ⟨X,s,normalized_component_nonterminal_action d hquotient horbit hI hfit
    s hno hpair hNI ha hi⟩

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
