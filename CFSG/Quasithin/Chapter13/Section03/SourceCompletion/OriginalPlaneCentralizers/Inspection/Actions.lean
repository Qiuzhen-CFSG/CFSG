module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.Lie
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.RankOneBlocks

/-!
# Action-level inspection of the original plane component

The alternating and Lie-family cubic exclusions are applied to the full B.5
moved-section conclusion, preserving its literal action, offender subgroup,
markings and remaining source clauses. Only natural linear degrees two and
three, two copies of the natural degree-three module, and the symmetric-five
marking survive. In particular this also removes the natural-dual and repeated
binary degree-four and degree-five rows.

For the degree-two row, the original C.2.7 geometry supplies Q Sylow in JQ,
the marked Borel and the actual L₂-even/A₅ block alternative. Every other
row retains its original moved section for the subsequent field reductions.
The last theorem applies this inspection to the escaping component extracted
from the original plane centralizer. The remaining A₅ and linear-three
arguments, field reductions and final chief-factor contradiction stay with
the original plane-centralizer assembly; they are not conclusions of this file.

Source: Aschbacher--Smith 13.3.12, printed pp.889--890; B.5.1, pp.99--103;
C.2.7, pp.145--147.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
universe u v w

section Actions
variable {D : Type v} [Group D] {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)

/-- The three surviving irreducible action rows, with their source markings. -/
inductive PlaneIrreducibleCase (K H : Subgroup D) : Prop
  | linearTwo (F : BinaryField) (generated : H = K)
      (e : ActionEquiv (ρ.comp K.subtype) (linearNatural F 2))
      (offenders : ∀ A, IsBestOffender ρ A → ∃ S : Sylow 2 K,
        A = (S : Subgroup K).map K.subtype)
      (ratio : quadraticRatio ρ = 1)
  | linearThree (F : BinaryField) (generated : H = K)
      (e : ActionEquiv (ρ.comp K.subtype) (linearNatural F 3))
      (ratio : quadraticRatio ρ = 1 / 2)
  | symmetricFive
      (e : MarkedActionEquiv ρ H K (BinaryPermutation.naturalRepresentation (Fin 5))
        (alternatingGroup (Fin 5)))
      (offenders : ∀ A, IsBestOffender ρ A →
        ChapterB.Offenders.CaseAFamily 5
          ((A.subgroupOf H).map e.action.groupEquiv.toMonoidHom))
      (ratio : quadraticRatio ρ = 1)

/-- The surviving full moved-section rows after the plane cubic exclusions. -/
inductive PlaneActionCase (K : Subgroup D) (c : MovedSection ρ K) : Prop
  | irreducible (irrPlus : IsIrrPlus ρ K c.space.toSubmodule)
      (faithful : Function.Injective c.action)
      (irreducible : IsIrreducible (c.action.comp K.subtype))
      (source : PlaneIrreducibleCase c.action K (offenderSubgroup c.action))
      (extension : K = ⊤ ∨ (∀ S : Sylow 2 D, K ⊔ (S : Subgroup D) = ⊤) ∧
        OuterNaturalAction c.action)
  | doubleThree (F : BinaryField) (whole : K = ⊤)
      (e : ActionEquiv (c.space.toRepresentation.comp K.subtype)
        (repeated (linearNatural F 3) 2))
      (offenders : ∀ A, IsBestOffender c.space.toRepresentation A ↔
        IsFullAxisGroup F 3 ((A.subgroupOf K).map e.groupEquiv.toMonoidHom))
      (ratio : quadraticRatio ρ = 1)
/-- Surviving non-rank-one markings on the original moved section. -/
inductive PlaneHigherActionCase (K : Subgroup D) (c : MovedSection ρ K) : Prop
  | linearThree (F : BinaryField)
      (e : ActionEquiv (c.action.comp K.subtype) (linearNatural F 3))
  | doubleThree (F : BinaryField)
      (e : ActionEquiv (c.space.toRepresentation.comp K.subtype)
        (repeated (linearNatural F 3) 2))
  | symmetricFive
      (e : MarkedActionEquiv c.action (offenderSubgroup c.action) K
        (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))
end Actions

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]
section Inspection
variable {D : Type v} [Group D] {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]

private noncomputable def quotientCenterCongr {B C : Type*} [Group B] [Group C]
    (e : B ≃* C) : (B ⧸ center B) ≃* (C ⧸ center C) := by
  apply QuotientGroup.congr _ _ e
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (centerCongr e ⟨y,hy⟩).property
  · intro hx
    exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩

private theorem not_binary_linear (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : starImage J ((L ⊔ T).pCoreIn 2) J ≃* SL(n,ZMod 2)) : False := by
  rcases hn with rfl | rfl
  · exact s.not_alternatingEight_star d J j
      (e.trans (Atlas.Order20160A8.sl4TwoEquivPSL.trans
        Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm))
  · exact s.not_linearFive_star d J j e

private noncomputable def symplecticTwoEquiv :
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) ≃* alternatingGroup (Fin 6) := by
  let e := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  refine (e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  exact alternatingGroup.commutator_perm_eq (by norm_num)

private theorem inspect_irreducible (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J)
    (ρ : Representation (ZMod 2) D W) (K H : Subgroup D)
    (e : starImage J ((L ⊔ T).pCoreIn 2) J ≃* K)
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ K H) : PlaneIrreducibleCase ρ K H := by
  cases h with
  | linearTwo F hg a ho hr => exact .linearTwo F hg a ho hr
  | linearThree F hg a hr => exact .linearThree F hg a hr
  | symplectic F large _ a _ => exact (s.not_symplectic_star d J j F large (e.trans a.groupEquiv)).elim
  | symplecticTwo a _ => exact (s.not_alternating_star d J j (Or.inl rfl)
      (e.trans (a.subgroupEquiv.trans symplecticTwoEquiv))).elim
  | g2 F large _ a _ _ => exact (s.not_g2_star d J j F large (e.trans a.groupEquiv)).elim
  | g2Two a _ _ => exact (s.not_g2DerivedTwo_star d J j (e.trans a.subgroupEquiv)).elim
  | symmetric n hn a ho hr =>
    rcases hn with rfl | rfl
    · exact .symmetricFive a ho hr
    · exact (s.not_alternating_star d J j (Or.inr rfl) (e.trans a.subgroupEquiv)).elim
  | alternatingSix _ a _ _ => exact (s.not_alternating_star d J j (Or.inl rfl) (e.trans a.groupEquiv)).elim
  | alternatingSeven _ _ a _ _ _ => exact (s.not_alternating_star d J j (Or.inr rfl) (e.trans a)).elim
  | tripleSix _ a _ => exact (s.not_tripleSix_star d J j
      ((quotientCenterCongr e).trans a.quotientEquiv)).elim
  | binaryLinear n hn _ a _ => exact (not_binary_linear s d J j hn (e.trans a.groupEquiv)).elim
  | orthogonalSix _ _ a _ _ => exact (s.not_alternatingEight_star d J j (e.trans a.groupEquiv)).elim
  | symmetricEight _ a _ => exact (s.not_alternatingEight_star d J j (e.trans a.subgroupEquiv)).elim
  | exteriorFive _ _ a _ _ _ => exact (s.not_linearFive_star d J j (e.trans a)).elim

private theorem inspect_action (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J)
    (ρ : Representation (ZMod 2) D W) (K : Subgroup D)
    (e : starImage J ((L ⊔ T).pCoreIn 2) J ≃* K)
    (c : MovedSection ρ K) (h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ K c) : PlaneActionCase ρ K c := by
  cases h with
  | irreducible hp hf hi hs he =>
    exact .irreducible hp hf hi (inspect_irreducible s d J j c.action K _ e hs) he
  | doubleThree F ht a ho hr => exact .doubleThree F ht a ho hr
  | naturalDual n hn _ ha =>
    obtain ⟨a⟩ := ha
    exact (not_binary_linear s d J j hn (e.trans a.groupEquiv)).elim
  | repeatedNatural n r hn _ _ _ ha =>
    obtain ⟨a⟩ := ha
    exact (not_binary_linear s d J j hn (e.trans a.groupEquiv)).elim

end Inspection

/-- Inspect the actual B.5 moved section while retaining its full source conclusion. -/
theorem Context.inspected_moved_section (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J) :
    let ρ := starRepresentation J ((L ⊔ T).pCoreIn 2)
    let B := offenderSubgroup ρ
    let K := (starImage J ((L ⊔ T).pCoreIn 2) J).subgroupOf B
    starImage J ((L ⊔ T).pCoreIn 2) J ≤ B ∧
      ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion (ρ.comp B.subtype) K,
        PlaneActionCase (ρ.comp B.subtype) K c.sectionData := by
  obtain ⟨hK,⟨c⟩⟩ := ChapterC.C27Source.star_moved_section_from_source j.input
  exact ⟨hK,c,inspect_action s d J j _ _ (subgroupOfEquivOfLe hK).symm _ c.clause_one⟩

/-- The natural rank-one branch supplies the actual block and Sylow placement;
all other branches retain their original moved-section markings. -/
theorem Context.block_or_linear_three_or_symmetric_five
    (s : Context T L V) (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J) :
    let ρ := starRepresentation J ((L ⊔ T).pCoreIn 2)
    let B := offenderSubgroup ρ
    let K := (starImage J ((L ⊔ T).pCoreIn 2) J).subgroupOf B
    (Chapter1.IsSylowIn 2 ((L ⊔ T).pCoreIn 2) (J ⊔ (L ⊔ T).pCoreIn 2) ∧
      IsRankOneBorel (starImage J ((L ⊔ T).pCoreIn 2) J)
        (starM J ((L ⊔ T).pCoreIn 2)
          (centralizer (d.A : Set G) ⊓ normalizer (L : Set G))) ∧
      ((∃ n, ChapterC.IsL2EvenBlock J n) ∨ ChapterC.IsAlternatingBlock J 5)) ∨
    ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion (ρ.comp B.subtype) K,
      PlaneHigherActionCase (ρ.comp B.subtype) K c.sectionData := by
  obtain ⟨hK,c,hc⟩ := s.inspected_moved_section d J j
  cases hc with
  | irreducible _ _ _ hi _ =>
    cases hi with
    | linearTwo F _ a ho hr =>
      obtain ⟨_,hm,hs,hb⟩ := ChapterC.C27Source.rankOne_row_blocks_from_source
        j.input hK c.sectionData F a hr ho
      exact Or.inl ⟨hs,hm,hb⟩
    | linearThree F _ a _ => exact Or.inr ⟨c,.linearThree F a⟩
    | symmetricFive a _ _ => exact Or.inr ⟨c,.symmetricFive a⟩
  | doubleThree F _ a _ _ => exact Or.inr ⟨c,.doubleThree F a⟩

/-- An escaping original plane centralizer supplies a component and a genuinely
inspected moved section, with the full B.5 source conclusion still attached. -/
theorem Context.exists_inspected_moved_section (s : Context T L V) (d : MarkedPlane V)
    (hout : ¬ centralizer (d.A : Set G) ≤ normalizer (L : Set G)) :
    ∃ J : Subgroup G, Nonempty (LocalData T L d J) ∧
      let ρ := starRepresentation J ((L ⊔ T).pCoreIn 2)
      let B := offenderSubgroup ρ
      let K := (starImage J ((L ⊔ T).pCoreIn 2) J).subgroupOf B
      starImage J ((L ⊔ T).pCoreIn 2) J ≤ B ∧
        ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
          (ρ.comp B.subtype) K, PlaneActionCase (ρ.comp B.subtype) K c.sectionData := by
  obtain ⟨J,⟨j⟩⟩ := s.localExtraction d hout
  exact ⟨J,⟨j⟩,s.inspected_moved_section d J j⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
