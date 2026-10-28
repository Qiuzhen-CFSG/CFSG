module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointSevenNormalizer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalDisplacement
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimpleContaining

/-!
# The containing component in the original point quotient is quasisimple

The nonquasisimple containing component would be the natural E₄₉-by-SL₂(7)
row. Its original smaller component is the centralizer of its unique
involution, so its normalizer has index dividing 49 and the full ambient
three-rank. At the original binary displacement point that normalizer has
three-rank at most one, whereas the point quotient has rank two.

This excludes both nonquasisimple A.3.6 rows at the actual original point.
The surviving proper quasisimple containing component retains the full
simple or central triple-cover catalogue; its proper embedding remains to
be excluded for original 15.3.23.

Source: Aschbacher--Smith A.3.6 and original 15.3.23,
printed pp.43--45 and 1128--1129.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree.OriginalSource ChapterC BinaryMS.MS93

/-- The rank gap at a normalizer excludes the nonquasisimple containing
component, using the same smaller binary-three section and full Sylow. -/
theorem binary_three_containing_quasisimple
    {X : Type*} [Group X] [Finite X]
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (hO : pCore 2 X = ⊥)
    (S : Sylow 2 X) {B K : Subgroup X}
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hK : K.IsCComponent) (hKn : K.Normal) (hBK : B ≤ K)
    (hSB : (S : Subgroup X) ≤ normalizer (B : Set X))
    (e : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (h3 : 2 ≤ primeRank 3 X)
    (hN : primeRank 3 (normalizer (B : Set X)) ≤ 1) : IsQuasisimple K := by
  by_contra hn
  obtain ⟨ha,hgen⟩ := binary_three_nonquasisimple_containing_seven hX hO S hB hK hBK e hn
  let := hKn
  let a := subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup X) from le_sup_left)
  let : Group.IsPerfect (B.subgroupOf (B ⊔ (S : Subgroup X))) := hB.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  let : IsSimpleGroup Matrix.PSL3Two.SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup (B ⧸ pCore 2 B) := eSL.isSimpleGroup
  have he := binary_three_seven_normalizer_rank K B hBK hgen ha S hSB
  rw [he] at hN
  omega

universe u
variable {G : Type u} [Group G] [Finite G]

private theorem point_quotient_sylow_normalizes
    (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (z : G) (hLS : L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C)) : Subgroup _) ≤
      normalizer ((L.subgroupOf C).map q : Set (C ⧸ pCore 2 C)) := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  have hLC : L ≤ C := le_sup_left.trans hLS
  have hSC : d.S ≤ C := le_sup_right.trans hLS
  have hSL : d.S ≤ normalizer (L : Set G) :=
    le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
      (show L ≤ L ⊔ d.S from le_sup_left)).mp b.component_normal)
  have hPe : (P : Subgroup C) = d.S.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hSC]
  have hPB : (P : Subgroup C) ≤ normalizer (L.subgroupOf C : Set C) := by
    rw [hPe,←subgroupOf_normalizer_eq hLC]
    exact comap_mono hSL
  exact (map_mono hPB).trans ((L.subgroupOf C).le_normalizer_map q)

/-- At the original large-distance displacement point the proper containing
component in the literal two-core quotient is quasisimple. All MS93 earlier
path premises are discharged, and the exact simple/triple-cover alternatives
retain the original point, quotient map, local component and full Sylow. -/
theorem binary_three_large_distance_point_quasisimple
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
          IsQuasisimple (K.map q) ∧
          ((IsSimpleGroup (K.map q) ∧ Chapter1.Section02.LocalModels.TheoremCModel (K.map q)) ∨
            (Nonempty (center (K.map q) ≃* Multiplicative (ZMod 3)) ∧
              Chapter1.Section02.LocalModels.ThreeCoverModel (K.map q))) := by
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  obtain ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,⟨he⟩,hr,hn,
    P,hP,hB,K,hK,hKn,hLK,hKq,hKnq,hBKq⟩ :=
    binary_three_source_point_quotient_strict_component
      hG d hempty hM hu hmany hI htwo hf c e b t common earlier g hgT hgS
  have hSB := point_quotient_sylow_normalizes d c.L b z hLS P hP
  let q := QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))
  have hquasi := binary_three_containing_quasisimple hsq hzero
    (P.mapSurjective (QuotientGroup.mk'_surjective _)) hB hKq hKnq hBKq.le hSB he
    hr.ge hn
  let : IsQuasisimple (K.map q) := hquasi
  have hmodels := ChapterA.Section03.SourceEmbeddings.quasisimple_containing_component_models_knownSimple
    hsq hzero hKq
  exact ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,⟨he⟩,hr,hn,
    P,hP,hB,K,hK,hKn,hLK,hKq,hKnq,hBKq,hquasi,hmodels⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
