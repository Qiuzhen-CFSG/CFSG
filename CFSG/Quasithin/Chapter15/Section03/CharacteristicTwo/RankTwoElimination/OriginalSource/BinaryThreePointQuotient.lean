module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointComponent
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.PCoreImage

/-!
# The literal binary local subgroup in the point centralizer quotient

The original plane stabilizer is Sylow in C = C_G(z). Quotienting C by
its two-core preserves the local C-component condition and the original
PSL3(2) quotient marking of L. The containing normal component also maps
to a normal C-component in this same quotient.

The selected involution belongs to the third lower-central subgroup of
[O₂(L),L] and to the center of C, so O₂(C) kills it. Counting the kernel on the
intrinsic four gives image order at most two. Prime-core and commutator
transport identify this image with the intrinsic third commutator of the
literal smaller subgroup in C/O₂(C).

The final theorem applies these reductions to the original binary source.
The MS93 Earlier facts remain explicit. The local embedding classification
and the argument returning to the original two-core remain separate.

Source: Aschbacher--Smith 1.2.4 and 15.3.23, printed pp.505,1128--1129;
Meierfrankenfeld--Stellmacher (1993), (4.5), printed pp.895--900.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open Chapter1 ChapterC BinaryMS.MS93 LinearThree.OriginalSource
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem central_involution_mem_twoCore (z : G) (hz : orderOf z = 2)
    (hc : z ∈ center G) : z ∈ pCore 2 G := by
  have hle : zpowers z ≤ center G := zpowers_le.mpr hc
  let : (zpowers z).Normal :=
    ⟨fun a ha b => by simpa [mem_center_iff.mp (hle ha) b] using ha⟩
  have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,hz]; rfl)
  exact (le_sSup ⟨inferInstance,hp⟩ : zpowers z ≤ pCore 2 G) (mem_zpowers z)

private theorem four_image_card_le_two_of_involution_kernel
    {D : Type u} [Group D] (H : Subgroup G) (hcard : Nat.card H = 4)
    (f : G →* D) (z : G) (hzH : z ∈ H) (hz : orderOf z = 2) (hf : f z = 1) :
    Nat.card (H.map f) ≤ 2 := by
  let q := f.subgroupMap H
  have hzq : (⟨z,hzH⟩ : H) ∈ q.ker := Subtype.ext hf
  have hl : zpowers (⟨z,hzH⟩ : H) ≤ q.ker := zpowers_le.mpr hzq
  have hker : 2 ≤ Nat.card q.ker := by
    have hh := card_le_of_le hl
    have hzo : orderOf (⟨z,hzH⟩ : H) = 2 :=
      (orderOf_injective H.subtype H.subtype_injective _).symm.trans hz
    rwa [Nat.card_zpowers,hzo] at hh
  have hc := q.ker.card_mul_index
  rw [index_ker,q.range_eq_top_of_surjective (f.subgroupMap_surjective H),card_top,hcard] at hc
  have hh := Nat.mul_le_mul_right (Nat.card (H.map f)) hker
  omega

/-- The actual local subgroup remains an original A.3 local component after
quotienting the point centralizer by its two-core. Its own two-core quotient
retains the original PSL3(2) marking. -/
theorem point_centralizer_quotient_local (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (z : G) (hLS : L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (L.subgroupOf C).map q
    B ∈ ChapterA.Section03.localCComponents
      (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))) ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) := by
  let C := centralizer ({z} : Set G)
  let J := L ⊔ d.S
  let q := QuotientGroup.mk' (pCore 2 C)
  have hLC : L ≤ C := le_sup_left.trans hLS
  have hSC : d.S ≤ C := le_sup_right.trans hLS
  have hPe : (P : Subgroup C) = d.S.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [map_subgroupOf_eq_of_le hSC]
    exact hP
  have hlocal : L ∈ ChapterA.Section03.localCComponents d.S := b.component
  have hlocalC : L.subgroupOf C ∈ ChapterA.Section03.localCComponents P := by
    rw [hPe]
    let a := (subgroupOfEquivOfLe hLS).symm
    have hh := hlocal.map_equiv a
    have he : (L.subgroupOf J).map a.toMonoidHom =
        (L.subgroupOf C).subgroupOf (J.subgroupOf C) := by
      ext x
      constructor
      · rintro ⟨l,hl,rfl⟩
        exact hl
      · intro hx
        exact ⟨⟨x,x.property⟩,hx,rfl⟩
    rw [he,subgroupOf_sup hLC hSC] at hh
    exact hh
  let := pCore_isNilpotent (p := 2) (G := C)
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  have hloc := Chapter1.Section02.localCComponents_map_of_solvable_ker hlocalC q
  refine ⟨?_,?_⟩
  · simpa only [Sylow.coe_mapSurjective] using hloc
  · let E := L.subgroupOf C
    have hk : IsPGroup 2 (q.subgroupMap E).ker := by
      rw [ker_subgroupMap,QuotientGroup.ker_mk']
      exact pCore_isPGroup.comap_subtype
    let a := subgroupOfEquivOfLe hLC
    exact ⟨((q.subgroupMap E).pCoreQuotientEquiv (q.subgroupMap_surjective E) hk).symm.trans
      ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e)⟩

/-- The central involution removes at least half of the literal intrinsic
four in the point centralizer's two-core quotient. -/
private theorem intrinsicFour_point_quotient_image_card (L : Subgroup G) (z : G)
    (hz : z ∈ intrinsicFour L) (hz2 : orderOf z = 2)
    (hcard : Nat.card (intrinsicFour L) = 4)
    (hH : intrinsicFour L ≤ centralizer ({z} : Set G)) :
    let C := centralizer ({z} : Set G)
    Nat.card ((intrinsicFour L).subgroupOf C |>.map (QuotientGroup.mk' (pCore 2 C))) ≤ 2 := by
  let C := centralizer ({z} : Set G)
  let zz : C := ⟨z,mem_centralizer_singleton_iff.mpr rfl⟩
  have hzz : orderOf zz = 2 := (orderOf_injective C.subtype C.subtype_injective zz).symm.trans hz2
  have hc : zz ∈ center C := by
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (mem_centralizer_singleton_iff.mp c.property)
  have hzcore := central_involution_mem_twoCore zz hzz hc
  have hHcard : Nat.card ((intrinsicFour L).subgroupOf C) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hH).toEquiv).trans hcard
  exact four_image_card_le_two_of_involution_kernel _ hHcard
    (QuotientGroup.mk' (pCore 2 C)) zz hz hzz
    ((QuotientGroup.eq_one_iff _).mpr hzcore)


private theorem intrinsicFour_map_of_twoKernel
    {D : Type u} [Group D] [Finite D] (f : G →* D) (hk : IsPGroup 2 f.ker)
    (L : Subgroup G) : (intrinsicFour L).map f = intrinsicFour (L.map f) := by
  simp only [intrinsicFour,LinearThree.commutatorCore,map_commutator,
    map_pCoreIn_of_ker_isPGroup f hk]

/-- The actual smaller subgroup in the point quotient has intrinsic third
commutator of order at most two. The identity uses its own two-core, so it
can be applied directly to a classification of that literal local subgroup. -/
theorem intrinsicFour_point_quotient_card (L : Subgroup G) (z : G)
    (hz : z ∈ intrinsicFour L) (hz2 : orderOf z = 2)
    (hcard : Nat.card (intrinsicFour L) = 4)
    (hLC : L ≤ centralizer ({z} : Set G)) :
    let C := centralizer ({z} : Set G)
    let B := (L.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C))
    Nat.card (intrinsicFour B) ≤ 2 := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  have hQ : LinearThree.commutatorCore L ≤ C :=
    (LinearThree.commutatorCore_le L).trans ((L.pCoreIn_le 2).trans hLC)
  have hQQ : ⁅LinearThree.commutatorCore L,LinearThree.commutatorCore L⁆ ≤
      LinearThree.commutatorCore L := (Subgroup.commutator_le_sup _ _).trans (sup_le le_rfl le_rfl)
  have hH : intrinsicFour L ≤ C :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le (hQQ.trans hQ) hQ)
  have hk : IsPGroup 2 C.subtype.ker := by
    rw [(MonoidHom.ker_eq_bot_iff C.subtype).mpr C.subtype_injective]
    exact IsPGroup.of_card (n := 0) (by simp)
  have hi : intrinsicFour (L.subgroupOf C) = (intrinsicFour L).subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [map_subgroupOf_eq_of_le hH]
    have hmapL : (L.subgroupOf C).map C.subtype = L := map_subgroupOf_eq_of_le hLC
    have hh := intrinsicFour_map_of_twoKernel C.subtype hk (L.subgroupOf C)
    rw [hmapL] at hh
    exact hh
  have hq : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  change Nat.card (intrinsicFour ((L.subgroupOf C).map q)) ≤ 2
  rw [← intrinsicFour_map_of_twoKernel q hq,hi]
  exact intrinsicFour_point_quotient_image_card L z hz hz2 hcard hH


/-- The original binary source supplies the literal local embedding problem
in the point centralizer modulo its two-core, including the shortened third
commutator and the normal containing component. The MS93 Earlier hypotheses
remain explicit; no embedding shortlist or quotient quasisimplicity is assumed. -/
theorem binary_three_source_point_quotient
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
      let C := centralizer ({z} : Set G)
      let q := QuotientGroup.mk' (pCore 2 C)
      let B := (c.L.subgroupOf C).map q
      IsSQTK KnownSimple.IsKnownSimple (C ⧸ pCore 2 C) ∧
      pCore 2 (C ⧸ pCore 2 C) = ⊥ ∧
      Nat.card (intrinsicFour B) ≤ 2 ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) ∧
      ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = d.S ∧
        B ∈ ChapterA.Section03.localCComponents
          (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))) ∧
        ∃ K : Subgroup C, K.IsCComponent ∧ K.Normal ∧ c.L.subgroupOf C ≤ K ∧
          (K.map q).IsCComponent ∧ (K.map q).Normal ∧ B ≤ K.map q := by
  obtain ⟨z,hz,hz2,hLS,_,hout,hsq,_,P,hP⟩ :=
    binary_three_source_point_sylow hG d hempty hM hu hmany hI htwo hf c e b t common earlier
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  obtain ⟨hloc,he⟩ := point_centralizer_quotient_local d c.L e b z hLS P hP
  obtain ⟨K,hK,hKn,hLK,_⟩ := point_centralizer_normal_component hG d c.L b z hz2 hLS ⟨P,hP⟩
  have hfour := intrinsicFour_properties_of_MS93 d c.L b t common earlier
  let : K.Normal := hKn
  let := pCore_isNilpotent (p := 2) (G := C)
  exact ⟨z,hz,hz2,hLS,hout,
    ChapterE.Structure.sqtk_two_quotient hsq (pCore 2 C) pCore_isPGroup,
    pCore_quotient_pCore_eq_bot 2,
    intrinsicFour_point_quotient_card c.L z hz hz2 hfour.2.1 (le_sup_left.trans hLS),
    he,P,hP,hloc,K,hK,hKn,hLK,hK.map_quotient (pCore 2 C),
    hKn.map q (QuotientGroup.mk'_surjective _),map_mono hLK⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
