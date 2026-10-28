module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.RankOneExclusion
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SylowNormalizerCubic

/-!
# The remaining rank-one fields in the original plane inspection

The specified cubic has order three and lies in both J and L. Its
membership in L makes it normalize Q = O₂(LT). When Q is Sylow in JQ,
restriction to the normal component gives a Sylow subgroup of J whose
normalizer contains this cubic. The actual natural block quotient then
forces the binary field degree to be even. The perpendicular-space
contradiction already excludes degree two, leaving even degrees at least
four, alongside the full odd-degree linear-three moved-section rows.

This is an inspection reduction. The remaining field-automorphism and
linear-three chief-factor arguments belong to the original plane-centralizer
assembly and are not assumed or asserted here.

Source: Aschbacher--Smith 13.3.12, printed pp.889--890.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- The marked cubic in L normalizes the original radical. Restricting its
Sylow placement to J forces the natural block field degree to be even. -/
theorem Context.rankOne_degree_even (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J) {m : ℕ}
    (hs : Chapter1.IsSylowIn 2 ((L ⊔ T).pCoreIn 2) (J ⊔ (L ⊔ T).pCoreIn 2))
    (hb : ChapterC.IsL2EvenBlock J m) : Even m := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let D := J ⊔ Q
  let J0 := J.subgroupOf D
  let : J0.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le J.le_normalizer j.input.normalizes)
  obtain ⟨S,hS⟩ := hs
  have hSQ : (S : Subgroup D) = Q.subgroupOf D := by
    apply map_injective D.subtype_injective
    rw [map_subgroupOf_eq_of_le (show Q ≤ D from le_sup_right)]
    exact hS
  obtain ⟨P0,hP0⟩ := S.exists_subgroupOf_eq_of_normal J0
  let e : J0 ≃* J := subgroupOfEquivOfLe le_sup_left
  let P := P0.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP : (P : Subgroup J) = Q.subgroupOf J := by
    change (P0 : Subgroup J0).map e.toMonoidHom = _
    rw [hP0,hSQ]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x,hx,e.apply_symm_apply x⟩
  obtain ⟨n,hnJ,hnL,ho,_⟩ := s.component_marked_cubic_order_three d J j
  have hnQ : n.val ∈ normalizer (Q : Set G) :=
    normalizer_le_normalizer_characteristic_image (L ⊔ (T : Subgroup G))
      (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        ((L ⊔ (T : Subgroup G)).le_normalizer (mem_sup_left hnL))
  apply hb.exponent_even_of_sylowNormalizer_cubic P ⟨n.val,hnJ⟩
  · change (⟨n.val,hnJ⟩ : J) ∈ normalizer ((P : Subgroup J) : Set J)
    rw [hP,mem_normalizer_iff]
    intro y
    exact mem_normalizer_iff.mp hnQ (y : G)
  · exact (Subgroup.orderOf_coe ⟨n.val,hnJ⟩).symm.trans ho

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- The remaining natural rank-one field degree is even and at least four;
the odd-degree linear-three cases retain their literal moved section. -/
theorem Context.large_even_block_or_odd_linearThree (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J) :
    let ρ := starRepresentation J ((L ⊔ T).pCoreIn 2)
    let B := offenderSubgroup ρ
    let K := (starImage J ((L ⊔ T).pCoreIn 2) J).subgroupOf B
    (Chapter1.IsSylowIn 2 ((L ⊔ T).pCoreIn 2) (J ⊔ (L ⊔ T).pCoreIn 2) ∧
      ∃ n, 4 ≤ n ∧ Even n ∧ ChapterC.IsL2EvenBlock J n) ∨
    ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp B.subtype) K, PlaneOddLinearThreeCase (ρ.comp B.subtype) K c.sectionData := by
  rcases s.remaining_block_or_odd_linearThree d J j with ⟨hs,n,hn,hb⟩ | hh
  · have he := s.rankOne_degree_even d J j hs hb
    have hn1 := hb.1
    refine Or.inl ⟨hs,n,?_,he,hb⟩
    obtain ⟨k,hk⟩ := he
    omega
  · exact Or.inr hh

/-- Apply the field-parity inspection to the component extracted from the
original escaping plane centralizer. -/
theorem Context.exists_large_even_block_or_odd_linearThree (s : Context T L V)
    (d : MarkedPlane V)
    (hout : ¬ centralizer (d.A : Set G) ≤ normalizer (L : Set G)) :
    ∃ J : Subgroup G, Nonempty (LocalData T L d J) ∧
      let ρ := starRepresentation J ((L ⊔ T).pCoreIn 2)
      let B := offenderSubgroup ρ
      let K := (starImage J ((L ⊔ T).pCoreIn 2) J).subgroupOf B
      (Chapter1.IsSylowIn 2 ((L ⊔ T).pCoreIn 2) (J ⊔ (L ⊔ T).pCoreIn 2) ∧
        ∃ n, 4 ≤ n ∧ Even n ∧ ChapterC.IsL2EvenBlock J n) ∨
      ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp B.subtype) K, PlaneOddLinearThreeCase (ρ.comp B.subtype) K c.sectionData := by
  obtain ⟨J,⟨j⟩⟩ := s.localExtraction d hout
  exact ⟨J,⟨j⟩,s.large_even_block_or_odd_linearThree d J j⟩
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
