module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointQuotient
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeCrossCore

/-!
# The opposite core in the original point-centralizer quotient

The original plane stabilizer S is Sylow in C = C_G(z). Hence O₂(C),
embedded in G, lies in O₂(LS). The original opposite commutator core
Qᵍ escapes O₂(LS), so its literal image D in C/O₂(C) is nontrivial.

The smaller local component image B cannot normalize D. If it did, the
full preimage of D would be a two-group normalized by LS and contained in S;
thus Qᵍ would lie in O₂(LS), contradicting the original normalizer argument.
The final consumer retains the actual point, local component, full Sylow,
normal containing component and shortened intrinsic third commutator.

These are constraints on the original ambient embedding problem, not the
large-distance exclusion. The remaining ambient contradiction and the
independent MS93 Earlier input are not asserted here.

Source: Aschbacher–Smith 15.3.6 and 15.3.23, printed pp.1122,1128–1129;
the point-quotient setup also uses original 1.2.4, printed p.505.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem point_core_le_original_core
    (L S C : Subgroup G) (hLS : L ⊔ S ≤ C)
    (P : Sylow 2 C) (hP : (P : Subgroup C).map C.subtype = S) :
    C.pCoreIn 2 ≤ (L ⊔ S).pCoreIn 2 := by
  have hQS : C.pCoreIn 2 ≤ S := hP ▸ pCoreIn_le_sylow C P
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 C) (hQS.trans le_sup_right)
    (hLS.trans (C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))))

omit [Finite G] in
private theorem two_image_not_normalized
    (L S Q C : Subgroup G) (hLS : L ⊔ S ≤ C)
    (P : Sylow 2 C) (hP : (P : Subgroup C).map C.subtype = S)
    (hQ : IsPGroup 2 Q) (hQS : Q ≤ S)
    (hSN : S ≤ normalizer (Q : Set G))
    (hout : ¬ Q ≤ (L ⊔ S).pCoreIn 2) :
    ¬ (L.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C)) ≤
      normalizer ((Q.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C)) : Set (C ⧸ pCore 2 C)) := by
  let J := L ⊔ S
  let q := QuotientGroup.mk' (pCore 2 C)
  let D := (Q.subgroupOf C).map q
  let U := D.comap q
  have hSC : S ≤ C := le_sup_right.trans hLS
  have hQC : Q ≤ C := hQS.trans hSC
  have hq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hU : IsPGroup 2 U := (hQ.comap_subtype.map q).comap_of_ker_isPGroup q hq
  have hSJ : (S.subgroupOf C).map q ≤ normalizer (D : Set (C ⧸ pCore 2 C)) := by
    apply (map_mono ?_).trans ((Q.subgroupOf C).le_normalizer_map q)
    rw [← subgroupOf_normalizer_eq hQC]
    exact comap_mono hSN
  intro hLN
  have hJN : (J.subgroupOf C).map q ≤ normalizer (D : Set (C ⧸ pCore 2 C)) := by
    rw [subgroupOf_sup (le_sup_left.trans hLS) hSC,Subgroup.map_sup]
    exact sup_le hLN hSJ
  have hJU : J.subgroupOf C ≤ normalizer (U : Set C) :=
    (map_le_iff_le_comap.mp hJN).trans (D.le_normalizer_comap q)
  have hUS : U ≤ (P : Subgroup C) := by
    have hD : D ≤ (P : Subgroup C).map q := by
      apply map_mono
      have hSP : S.subgroupOf C = (P : Subgroup C) := by
        apply map_injective C.subtype_injective
        rw [map_subgroupOf_eq_of_le hSC,hP]
      rw [←hSP]
      exact comap_mono hQS
    have hpC : q.ker ≤ (P : Subgroup C) := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.le_sylow_of_normal P
    exact (comap_mono hD).trans (comap_map_eq_self hpC).le
  have hUJ : U.map C.subtype ≤ J :=
    ((map_mono hUS).trans hP.le).trans le_sup_right
  have hnorm : J ≤ normalizer (U.map C.subtype : Set G) := by
    have hh := (map_mono hJU).trans (U.le_normalizer_map C.subtype)
    rwa [map_subgroupOf_eq_of_le hLS] at hh
  have hcore : U.map C.subtype ≤ J.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (hU.map C.subtype) hUJ hnorm
  apply hout
  intro x hx
  apply hcore
  exact mem_map_of_mem C.subtype
    (show (⟨x,hQC hx⟩ : C) ∈ U from mem_map_of_mem q hx)


/-- The opposite core survives in the literal point quotient and its image
is not normalized by the original local component image. -/
theorem binary_three_source_point_opposite_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (c.L.subgroupOf C).map q
    let D := (((LinearThree.commutatorCore c.L).conjBy g).subgroupOf C).map q
    C.pCoreIn 2 ≤ (c.L ⊔ d.S).pCoreIn 2 ∧
      D ≠ ⊥ ∧ IsPGroup 2 D ∧ ¬ B ≤ normalizer (D : Set (C ⧸ pCore 2 C)) := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let Q := (LinearThree.commutatorCore c.L).conjBy g
  obtain ⟨hQS,hN,hout⟩ := binary_three_source_conjugate_core_nonvanishing
    hG d hempty hM hu hmany hI htwo hf c e g hgT hgS
  have hpQ : IsPGroup 2 Q := d.T.isPGroup'.to_le (hQS.trans inf_le_left)
  have hcore := point_core_le_original_core c.L d.S C hLS P hP
  have hQC : Q ≤ C := hQS.trans (le_sup_right.trans hLS)
  have hnon : ¬ (c.L.subgroupOf C).map q ≤ normalizer
      ((Q.subgroupOf C).map q : Set (C ⧸ pCore 2 C)) :=
    two_image_not_normalized c.L d.S Q C hLS P hP hpQ hQS
      (le_sup_right.trans hN) hout
  refine ⟨hcore,?_,hpQ.comap_subtype.map q,hnon⟩
  intro hz
  apply hout
  intro x hx
  have hh : q (⟨x,hQC hx⟩ : C) = 1 :=
    hz.le (mem_map_of_mem q (show (⟨x,hQC hx⟩ : C) ∈ Q.subgroupOf C from hx))
  exact hcore (mem_map_of_mem C.subtype ((QuotientGroup.eq_one_iff _).mp hh))

/-- The original source point quotient retains the smaller PSL₃(2) local
component, its shortened third commutator, and a surviving opposite two-group
which it does not normalize. The only earlier MS input is explicit. -/
theorem binary_three_source_point_quotient_opposite_pair
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
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ z : G, z ∈ intrinsicFour c.L ∧ orderOf z = 2 ∧
      c.L ⊔ d.S ≤ centralizer ({z} : Set G) ∧
      ¬ centralizer ({z} : Set G) ≤ d.M ∧
      let C := centralizer ({z} : Set G)
      let q := QuotientGroup.mk' (pCore 2 C)
      let B := (c.L.subgroupOf C).map q
      let D := (((LinearThree.commutatorCore c.L).conjBy g).subgroupOf C).map q
      IsSQTK KnownSimple.IsKnownSimple (C ⧸ pCore 2 C) ∧
      pCore 2 (C ⧸ pCore 2 C) = ⊥ ∧
      Nat.card (intrinsicFour B) ≤ 2 ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) ∧
      C.pCoreIn 2 ≤ (c.L ⊔ d.S).pCoreIn 2 ∧
      D ≠ ⊥ ∧ IsPGroup 2 D ∧ ¬ B ≤ normalizer (D : Set (C ⧸ pCore 2 C)) ∧
      ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = d.S ∧
        B ∈ ChapterA.Section03.localCComponents
          (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))) ∧
        ∃ K : Subgroup C, K.IsCComponent ∧ K.Normal ∧ c.L.subgroupOf C ≤ K ∧
          (K.map q).IsCComponent ∧ (K.map q).Normal ∧ B ≤ K.map q := by
  obtain ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,he,P,hP,hB,K,hK,hKn,hLK,hKq,hKnq,hBKq⟩ :=
    binary_three_source_point_quotient hG d hempty hM hu hmany hI htwo hf c e b t common earlier
  obtain ⟨hcore,hD,hDtwo,hBD⟩ := binary_three_source_point_opposite_core
    hG d hempty hM hu hmany hI htwo hf c e z hLS P hP g hgT hgS
  exact ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,he,hcore,hD,hDtwo,hBD,
    P,hP,hB,K,hK,hKn,hLK,hKq,hKnq,hBKq⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
