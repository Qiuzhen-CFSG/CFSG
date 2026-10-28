module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointSylow
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality

/-!
# A normal component in the original binary point centralizer

The actual plane stabilizer is Sylow in C_G(z), and it normalizes the
original local component L. Source1.2.4 applied inside this centralizer
therefore gives a unique containing C-component, normal in C_G(z).
SQTK is obtained on the literal quotient by its two-core, so the local
containment and normality theorems apply with their original markings.

The final consumer uses the full binary source input and retains the
outside-centralizer and three-rank conclusions. The reduced MS93 earlier
hypotheses remain explicit; subsequent component exclusion is separate.

Source: Aschbacher--Smith1.2.4 and15.3.6, in the setting of15.3.23,
printed pp.1122 and1128--1129.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open Chapter1 ChapterC BinaryMS.MS93 LinearThree.OriginalSource
universe u
variable {G : Type u} [Group G] [Finite G]


theorem point_centralizer_normal_component (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (z : G) (hz : orderOf z = 2)
    (hLS : L ⊔ d.S ≤ centralizer ({z} : Set G))
    (hs : Chapter1.IsSylowIn 2 d.S (centralizer ({z} : Set G))) :
    let C := centralizer ({z} : Set G)
    ∃ K : Subgroup C, K.IsCComponent ∧ K.Normal ∧ L.subgroupOf C ≤ K ∧
      ∀ D : Subgroup C, D.IsCComponent → L.subgroupOf C ≤ D → D = K := by
  let C := centralizer ({z} : Set G)
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
  have hQ := ChapterE.Structure.sqtk_two_quotient
    (hG.involution_centralizer_sqtk hz) (pCore 2 C) pCore_isPGroup
  obtain ⟨K,⟨hK,hLK,hKn⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source hQ P hB hPB
  refine ⟨K,hK,hKn,hLK,?_⟩
  obtain ⟨K',⟨hK',hLK'⟩,hu⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_of_A_3_12
      (fun _ _ _ => ChapterA.Section03.SourceComponents.containment_knownSimple) hQ P hB
  intro D hD hLD
  exact (hu D ⟨hD,hLD⟩).trans (hu K ⟨hK,hLK⟩).symm

/-- The original binary source has a unique normal component over L in an outside involution centralizer. -/
theorem binary_three_source_point_component
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
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    ∃ z : G, z ∈ intrinsicFour c.L ∧ orderOf z = 2 ∧
      c.L ⊔ d.S ≤ centralizer ({z} : Set G) ∧
      ¬ centralizer ({z} : Set G) ≤ d.M ∧
      IsSQTK KnownSimple.IsKnownSimple (centralizer ({z} : Set G)) ∧
      primeRank 3 (centralizer ({z} : Set G)) ≤ 2 ∧
      let C := centralizer ({z} : Set G)
      ∃ K : Subgroup C, K.IsCComponent ∧ K.Normal ∧ c.L.subgroupOf C ≤ K ∧
        ∀ D : Subgroup C, D.IsCComponent → c.L.subgroupOf C ≤ D → D = K := by
  obtain ⟨z,hz,hz2,hLS,_,hout,hsq,h3,P,hP⟩ :=
    binary_three_source_point_sylow hG d hempty hM hu hmany hI htwo hf c e b t common earlier
  exact ⟨z,hz,hz2,hLS,hout,hsq,h3,
    point_centralizer_normal_component hG d c.L b z hz2 hLS ⟨P,hP⟩⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
