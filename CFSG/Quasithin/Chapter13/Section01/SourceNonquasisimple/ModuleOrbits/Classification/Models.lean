module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.Component
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Preparation.ComponentRanks
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree
public import Theory.SpecificGroups.PSL2.PrimeCubicRank
public import Theory.SpecificGroups.PSL2.PrimeCoverCartanNormalizer
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import Theory.GroupTheory.PrimeRankSquareFree
public import Theory.SpecificGroups.PSL2.RootTwoRank
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.PSL3.OddDegreeProjectiveComparison

/-!
# The two actual component images in 13.1.10

The full B.5.5 component list is intersected with the two-rank two and
three-rank one of prime-field PSL₂. Three-rank eliminates every family except
binary SL₂ and SL₃ in odd field degree. Root-subgroup two-ranks then force
field orders four and two, respectively. The order-six endpoint is excluded
because its order is not divisible by four.

The final theorem applies this calculation to the actual reduced component
inside the offender actor, then uses the compatible radical quotient to
identify the image on U. These are actual matrix-group isomorphisms. The
four module clauses of 13.1.10 still require their separate construction.
The retained Thompson movement premise is owned by `qt-d-1317-supplements`.
Source: Aschbacher--Smith 13.1.10, printed pp.871--872, and B.5.5(1iv).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
open ComponentReduction.PreliminaryActions.Preparation ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Prime-field PSL₂ supplies exactly the source two- and three-ranks. -/
theorem prime_model_ranks {D : Type*} [Group D] [Finite D]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hm : ClassicalGroup.IsPSL D 2 p) :
    primeRank 2 D = 2 ∧ primeRank 3 D = 1 := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let ef : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, hc, ZMod.card])
  let eq := e.trans (Atlas.fieldEquivPSL 2 ef)
  constructor
  · rw [primeRank_equiv 2 eq]
    exact Theory.PSL2.primeField_two_rank hp3
  · apply le_antisymm
    · rw [primeRank_equiv 3 eq]
      exact Theory.PSL2.primeField_odd_rank (by decide)
    · exact Theory.PSL2.prime_model_three_rank_pos hp (hp.odd_of_ne_two (by omega)) hc e

/-- Intersect the genuine B.5.5 list with the prime-field PSL₂ ranks. -/
theorem small_models_of_componentModels {D : Type*} [Group D] [Finite D]
    {K : Subgroup D} (hm : ComponentModels K)
    (hr2 : primeRank 2 K = 2) (hr3 : primeRank 3 K = 1) :
    ClassicalGroup.IsPSL K 2 4 ∨ ClassicalGroup.IsPSL K 3 2 := by
  rcases componentModels_of_three_rank_one hm hr3 with ⟨F, ⟨e⟩⟩ | ⟨F, ho, ⟨e⟩⟩
  · have hle : F.degree ≤ 2 := by
      have hr := Theory.PSL2.root_two_rank_ge F.Carrier F.card_eq
      rw [primeRank_equiv 2 (e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL))] at hr2
      omega
    have hne : F.degree ≠ 1 := by
      intro he
      let es := e.trans ((ExtensionConsequences.degreeOneNaturalEquiv F he 2).groupEquiv.trans
        ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans
          BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree))
      have hc : Nat.card K = 6 := by
        rw [Nat.card_congr es.toEquiv]
        simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
      have hd : primeRank 2 K ≤ 1 := primeRank_le_one_of_square_not_dvd
        (by rw [hc]; norm_num)
      omega
    have he : F.degree = 2 := by have := F.degree_pos; omega
    exact Or.inl ⟨F.Carrier, inferInstance, inferInstance,
      by rw [F.card_eq, he]; norm_num,
      ⟨e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL⟩⟩
  · let eq := e.trans (Matrix.PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv F.card_eq ho)
    have hr := Matrix.PSL3Even.two_rank F.Carrier F.degree_pos F.card_eq
    rw [primeRank_equiv 2 eq] at hr2
    have he : F.degree = 1 := by omega
    exact Or.inr ⟨F.Carrier, inferInstance, inferInstance,
      by rw [F.card_eq, he]; norm_num, ⟨eq⟩⟩

/-- The source component image is L₂(4) or L₃(2), with actual isomorphisms. -/
theorem moved_component_small_models
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    ClassicalGroup.IsPSL (componentImage L) 2 4 ∨
      ClassicalGroup.IsPSL (componentImage L) 3 2 := by
  have hj := componentImage_le_reducedOffender h hL hn hmove
  let e := (subgroupOfEquivOfLe hj).trans (reducedImageEquivMovedImage h hmany hL hn)
  obtain ⟨p, hp, hp3, hm⟩ := moved_component_pslTwo h hmany hL hn
  obtain ⟨hr2, hr3⟩ := prime_model_ranks hp hp3 (hm.of_mulEquiv e)
  exact (small_models_of_componentModels (reducedOffender_componentModels h hmany hL hn hmove)
    hr2 hr3).imp (fun hm => hm.of_mulEquiv e.symm) (fun hm => hm.of_mulEquiv e.symm)

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
