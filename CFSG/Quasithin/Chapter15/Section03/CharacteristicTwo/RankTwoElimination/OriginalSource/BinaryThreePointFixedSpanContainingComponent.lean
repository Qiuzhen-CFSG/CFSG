module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointComponent
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.SourceSQTK
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanOutside
/-!
# Containing components in binary source outside overgroups

The marked binary source remains a local C-component at the same full
Sylow in any outside overgroup containing LS. The original source 1.2.4
therefore supplies a unique normal containing C-component. This uses the
SQTK two-core quotient of that actual outside overgroup and does not
assume the overgroup has characteristic two.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open Chapter1 ChapterC
universe u
variable {G : Type u} [Group G] [Finite G]
/-- An actual outside overgroup with the marked full Sylow has a unique
normal C-component containing the original binary source component. -/
theorem binary_three_source_outside_normal_component (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (C : Subgroup G) (hC : C ∈ d.Hplus)
    (hLS : L ⊔ d.S ≤ C)
    (hs : Chapter1.IsSylowIn 2 d.S C) :
    ∃ K : Subgroup C, K.IsCComponent ∧ K.Normal ∧ L.subgroupOf C ≤ K ∧
      ∀ D : Subgroup C, D.IsCComponent → L.subgroupOf C ≤ D → D = K := by
  let J := L ⊔ d.S
  have hLC : L ≤ C := le_sup_left.trans hLS
  have hSC : d.S ≤ C := le_sup_right.trans hLS
  have hcore : pCore 2 J ≠ ⊥ := by
    intro hb
    have htop : (⊤ : Subgroup J) ≤ ⊥ := by
      intro x _
      have hx : x ∈ centralizer (pCore 2 J : Set J) := by
        rw [hb]
        intro y hy
        have hy1 : y = 1 := hy
        simp [hy1]
      have hh := b.core_selfCentralizing hx
      rwa [hb] at hh
    exact b.component.ne_bot (bot_unique (le_top.trans htop))
  have hlocal : L ∈ Chapter1.L G d.S := by
    refine ⟨b.component,hs.restrict le_sup_right hLS,?_⟩
    exact fun hb => hcore ((map_eq_bot_iff_of_injective _ J.subtype_injective).mp hb)
  obtain ⟨P,hP⟩ := hs
  have hPe : (P : Subgroup C) = d.S.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [map_subgroupOf_eq_of_le hSC]
    exact hP
  have hB : L.subgroupOf C ∈ Chapter1.L C P := by
    rw [hPe]
    exact (Chapter1.mem_LIn_iff_subgroupOf hSC hLC).mp ⟨hLC,hlocal⟩
  have hSL : d.S ≤ normalizer (L : Set G) :=
    le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
      (show L ≤ J from le_sup_left)).mp b.component_normal)
  have hPB : (P : Subgroup C) ≤ normalizer (L.subgroupOf C : Set C) := by
    rw [hPe, ← subgroupOf_normalizer_eq hLC]
    exact comap_mono hSL
  have hQ := OutsideStructure.outside_twoCoreQuotient_sqtk hG d hC
  obtain ⟨K,⟨hK,hLK,hKn⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source hQ P hB hPB
  refine ⟨K,hK,hKn,hLK,?_⟩
  obtain ⟨K',⟨hK',hLK'⟩,hu⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_of_A_3_12
      (fun _ _ _ => ChapterA.Section03.SourceComponents.containment_knownSimple) hQ P hB
  intro D hD hLD
  exact (hu D ⟨hD,hLD⟩).trans (hu K ⟨hK,hLK⟩).symm


open scoped MatrixGroups IsMulCommutative
open LinearThree LinearThree.OriginalSource CoreActions BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

/-- The original fixed-span normalizer contains a unique normal C-component
above the original L, with no characteristic-two premise on the normalizer. -/
theorem binary_three_source_fixed_span_containing_component
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
    (z : G) (hzH : z ∈ LinearThree.OriginalSource.intrinsicFour c.L)
    (hz2 : orderOf z = 2) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G)))
    (hK : K.IsCComponent) (hKn : K.Normal)
    (hLK : c.L.subgroupOf (centralizer ({z} : Set G)) ≤ K)
    [IsSimpleGroup (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))]
    (eB : (((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) ⧸
      pCore 2 ((c.L.subgroupOf (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))) ≃* PSL(3,ZMod 2))
    (hrX : primeRank 3 (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))) = 2)
    (hrB : primeRank 3 (normalizer ((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) :
        Set ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))) ≤ 1)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) 4 2) :
    let U := conjugateSpanBy (intrinsicFour c.L) (centralizer ({z} : Set G))
    let A := normalizer (U : Set G)
    ∃ D : Subgroup A, D.IsCComponent ∧ D.Normal ∧ c.L.subgroupOf A ≤ D ∧
      ∀ E : Subgroup A, E.IsCComponent → c.L.subgroupOf A ≤ E → E = D := by
  let U := conjugateSpanBy (intrinsicFour c.L) (centralizer ({z} : Set G))
  let A := normalizer (U : Set G)
  have hout := binary_three_source_fixed_span_outside
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  exact binary_three_source_outside_normal_component hG d c.L b A hout.2.2.1
    hout.2.1 hout.2.2.2.1

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
