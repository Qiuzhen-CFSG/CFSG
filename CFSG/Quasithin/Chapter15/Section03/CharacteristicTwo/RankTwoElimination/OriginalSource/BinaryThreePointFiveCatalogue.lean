module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFiveExclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointA7Exclusion

/-!
# The actual point catalogue excludes PSL5(2)

The preserved full source packet now records the genuine PSL5 exclusion
alongside A7, with the same point, full Sylow, quotient, strict containing
component and complete finite catalogue.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The full original point packet retains its actual Sylow, quotient,
strict component containment and finite catalogue, with A7 and PSL5(2) now excluded. -/
theorem binary_three_large_distance_point_finite_models_not_a7_or_five
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ z : G, z ∈ intrinsicFour c.L ∧ orderOf z = 2 ∧
      c.L ⊔ d.S ≤ centralizer ({z} : Set G) ∧
      ¬ centralizer ({z} : Set G) ≤ d.M ∧
      let C := centralizer ({z} : Set G)
      let q := QuotientGroup.mk' (pCore 2 C)
      let B := (c.L.subgroupOf C).map q
      IsSQTK KnownSimple.IsKnownSimple (C ⧸ pCore 2 C) ∧
      pCore 2 (C ⧸ pCore 2 C) = ⊥ ∧
      Nat.card (intrinsicFour B) ≤ 2 ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) ∧
      primeRank 3 (C ⧸ pCore 2 C) = 2 ∧
      primeRank 3 (normalizer (B : Set (C ⧸ pCore 2 C))) ≤ 1 ∧
      ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = d.S ∧
        B ∈ ChapterA.Section03.localCComponents
          (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))) ∧
        (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C)) : Subgroup _) ≤
          normalizer (B : Set (C ⧸ pCore 2 C)) ∧
        Nonempty (((B ⊔ (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C)) :
          Subgroup (C ⧸ pCore 2 C)) : Subgroup (C ⧸ pCore 2 C)) ⧸
          pCore 2 (B ⊔ (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C)) :
            Subgroup (C ⧸ pCore 2 C)) : Subgroup (C ⧸ pCore 2 C))) ≃*
          PSL(3,ZMod 2)) ∧
        ∃ K : Subgroup C, K.IsCComponent ∧ K.Normal ∧ c.L.subgroupOf C ≤ K ∧
          (K.map q).IsCComponent ∧ (K.map q).Normal ∧ B < K.map q ∧
          IsSimpleGroup (K.map q) ∧ BinaryThreeFiniteSimpleCarrier (K.map q) ∧
          ¬ IsAlternating (K.map q) 7 ∧ ¬ ClassicalGroup.IsPSL (K.map q) 5 2 := by
  obtain ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,he,hr,hn,
    P,hP,hB,hSB,hjoin,K,hK,hKn,hLK,hKq,hKnq,hBKq,hsimple,hmodel,hnotA7⟩ :=
    binary_three_large_distance_point_finite_models_not_a7
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb g hgT hgS
  refine ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,he,hr,hn,
    P,hP,hB,hSB,hjoin,K,hK,hKn,hLK,hKq,hKnq,hBKq,hsimple,hmodel,hnotA7,?_⟩
  let := hKnq
  intro hm
  have hz1 : z ≠ 1 := by intro h; simp only [h,orderOf_one] at hz2; omega
  exact binary_three_source_point_not_psl_five
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hz hz1 hLS P hP
    (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) hBKq.le hm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
