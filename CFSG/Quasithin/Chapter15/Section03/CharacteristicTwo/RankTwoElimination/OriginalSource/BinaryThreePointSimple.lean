module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointQuasisimple
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCenter

/-!
# The actual simple carrier above the original binary point component

At the original large-distance point, the containing normal component has
a simple Theorem C carrier. The natural seven-core and central three-cover
alternatives have both been excluded using the original normalizer's cubic
rank bound. The point, full Sylow, smaller local component, quotient map,
and proper containment are unchanged throughout.

The remaining ambient embedding of the smaller PSL₃(2) section in that
simple carrier is still an obligation of original 15.3.23. This theorem
does not assume or assert a universal binary MS classification.

Source: Aschbacher--Smith A.3.6 and 15.3.23,
printed pp.43--45 and 1128--1129.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original large-distance source leaves a proper local binary-three
component in an actual simple containing component. Both nonsimple carrier
alternatives and all earlier MS93 path premises are discharged. -/
theorem binary_three_large_distance_point_simple
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
        ∃ K : Subgroup C, K.IsCComponent ∧ K.Normal ∧ c.L.subgroupOf C ≤ K ∧
          (K.map q).IsCComponent ∧ (K.map q).Normal ∧ B < K.map q ∧
          IsSimpleGroup (K.map q) ∧
          Chapter1.Section02.LocalModels.TheoremCModel (K.map q) := by
  obtain ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,⟨he⟩,hr,hn,
    P,hP,hB,K,hK,hKn,hLK,hKq,hKnq,hBKq,hquasi,_⟩ :=
    binary_three_large_distance_point_quasisimple
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb g hgT hgS
  let q := QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))
  let : IsQuasisimple (K.map q) := hquasi
  obtain ⟨hsimple,hmodel⟩ := binary_three_containing_simple_models hsq hzero hKq hBKq.le he hn
  exact ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,⟨he⟩,hr,hn,
    P,hP,hB,K,hK,hKn,hLK,hKq,hKnq,hBKq,hsimple,hmodel⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
