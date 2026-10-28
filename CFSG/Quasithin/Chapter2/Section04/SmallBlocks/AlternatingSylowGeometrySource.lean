module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingExtraspecialSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSylowSource
public import Theory.SpecificGroups.SymmetricFourWreath.CentralFactorGeometry
/-!
# The original Borel core inside the selected Sylow subgroup

The two-core of the Borel residual is normalized by the selected Sylow
subgroup. Its extraspecial center becomes the intersection of the Frattini
subgroup and center in the marked wreath model, hence is central in the
ambient Sylow subgroup. The core together with the marked central factor
is characteristic in the selected Sylow subgroup.

Source: Aschbacher–Smith 2.4.29, printed pp.544–545.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2
open ChapterC
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
theorem MinimalBlockSetup.single_borel_core_placement
    (d : MinimalBlockSetup M) (hsingle : d.L0 = d.block) :
    let B := M ⊓ d.block.map d.H.subtype
    let K := (pResidual 2 B).map B.subtype
    K.pCoreIn 2 ≤ (d.S : Subgroup d.H).map d.H.subtype ∧
      (d.S : Subgroup d.H).map d.H.subtype ≤ normalizer (K.pCoreIn 2 : Set G) := by
  let L := d.block.map d.H.subtype
  let B := M ⊓ L
  let K := (pResidual 2 B).map B.subtype
  let P := K.pCoreIn 2
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let : d.block.Normal := hsingle ▸ d.L0_normal
  have hHL : d.H ≤ normalizer (L : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      d.block.le_normalizer_map d.H.subtype
  have hRM : R ≤ M := d.full_pair.1.1.2.1
  have hRB : R ≤ normalizer (B : Set G) :=
    (le_inf (hRM.trans M.le_normalizer) ((map_subtype_le _).trans hHL)).trans
      inf_normalizer_le_normalizer_inf
  have hRK : R ≤ normalizer (K : Set G) :=
    hRB.trans (normalizer_le_normalizer_characteristic_image B (pResidual 2 B))
  have hRP : R ≤ normalizer (P : Set G) :=
    hRK.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hPH : P ≤ d.H := (pCoreIn_le 2 K).trans
    ((map_subtype_le _).trans (inf_le_right.trans (map_subtype_le _)))
  have hPi : IsPGroup 2 (P.subgroupOf d.H) :=
    (isPGroup_pCoreIn 2 K).of_equiv (subgroupOfEquivOfLe hPH).symm
  have hSi : (d.S : Subgroup d.H) ≤ normalizer (P.subgroupOf d.H : Set d.H) := by
    apply le_normalizer_iff.mpr
    intro s hs p hp
    exact (mem_normalizer_iff.mp (hRP (mem_map_of_mem d.H.subtype hs)) (p:G)).mp hp
  have hPS : P.subgroupOf d.H ≤ (d.S : Subgroup d.H) :=
    sup_eq_right.mp (d.S.is_maximal' (hPi.to_sup_of_normal_left' d.S.isPGroup' hSi) le_sup_right)
  refine ⟨?_,hRP⟩
  have hh := map_mono (f:=d.H.subtype) hPS
  rwa [map_subgroupOf_eq_of_le hPH] at hh

theorem MinimalBlockSetup.single_alternating_core_frattini_center_of_sylow_model
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    {D : Type*} [Group D] [Finite D] [IsElementaryAbelian 2 D]
    (e : ((d.S : Subgroup d.H).map d.H.subtype) ≃* SymmetricFourWreath.P × D) :
    let B := M ⊓ d.block.map d.H.subtype
    let K := (pResidual 2 B).map B.subtype
    let P := K.pCoreIn 2
    let R := (d.S : Subgroup d.H).map d.H.subtype
    (center P).map P.subtype = (frattini R ⊓ center R).map R.subtype := by
  let B := M ⊓ d.block.map d.H.subtype
  let K := (pResidual 2 B).map B.subtype
  let P := K.pCoreIn 2
  let R := (d.S : Subgroup d.H).map d.H.subtype
  obtain ⟨hPR,hRP⟩ := d.single_borel_core_placement hsingle
  let Q := P.subgroupOf R
  let eQ : Q ≃* P := subgroupOfEquivOfLe hPR
  let : Q.Normal := (normal_subgroupOf_iff_le_normalizer hPR).mpr hRP
  obtain ⟨hp⟩ := d.single_alternating_borel_core_quaternion hG T hST hsingle hA
  let hq := hp.map eQ.symm
  let : IsExtraspecial 2 Q := hq.extraspecial
  have hh := SymmetricFourWreath.center_eq_frattini_inf_center_of_equiv_prod e Q
  have hcenter := congrArg (map R.subtype) hh
  rw [map_map] at hcenter
  change (center P).map P.subtype = (frattini R ⊓ center R).map R.subtype
  rw [←center_map_equiv eQ,map_map]
  exact hcenter

theorem MinimalBlockSetup.single_alternating_core_center_in_T_of_sylow_model
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    {D : Type*} [Group D] [Finite D] [IsElementaryAbelian 2 D]
    (e : ((d.S : Subgroup d.H).map d.H.subtype) ≃* SymmetricFourWreath.P × D) :
    let B := M ⊓ d.block.map d.H.subtype
    let K := (pResidual 2 B).map B.subtype
    let P := K.pCoreIn 2
    (center P).map P.subtype ≤ (center (T : Subgroup G)).map (T : Subgroup G).subtype := by
  let B := M ⊓ d.block.map d.H.subtype
  let K := (pResidual 2 B).map B.subtype
  let P := K.pCoreIn 2
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let Z := (center P).map P.subtype
  have hPR : P ≤ R := (d.single_borel_core_placement hsingle).1
  have hZT : Z ≤ (T : Subgroup G) := (map_subtype_le _).trans (hPR.trans hST.le)
  have hi := (d.single_alternating_sylow_index_source hG T hM hTM hu hST hsingle hA).1
  let : (R.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hi
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hST.le).mp inferInstance
  let F := frattini R ⊓ center R
  let : F.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    exact ⟨characteristic_iff_le_comap.mp inferInstance a hx.1,
      characteristic_iff_le_comap.mp inferInstance a hx.2⟩
  have hZF : Z = F.map R.subtype :=
    d.single_alternating_core_frattini_center_of_sylow_model hG T hST hsingle hA e
  have hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G) := by
    rw [hZF]
    exact hTR.trans (normalizer_le_normalizer_characteristic_image R F)
  let : (Z.subgroupOf (T : Subgroup G)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hZT).mpr hTZ
  obtain ⟨hp⟩ := d.single_alternating_borel_core_quaternion hG T hST hsingle hA
  have hc : Nat.card (Z.subgroupOf (T : Subgroup G)) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZT).toEquiv,
      card_map_of_injective P.subtype_injective,hp.center_card]
  have hcent := central_of_normal_card_two (Z.subgroupOf (T : Subgroup G)) hc
  have hm := map_mono (f:=(T : Subgroup G).subtype) hcent
  rw [map_subgroupOf_eq_of_le hZT] at hm
  exact hm

theorem MinimalBlockSetup.single_alternating_core_factor_normalized_of_sylow_model
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    {D : Type*} [Group D] [Finite D] [IsElementaryAbelian 2 D]
    (e : ((d.S : Subgroup d.H).map d.H.subtype) ≃* SymmetricFourWreath.P × D)
    (E : Subgroup G) (hER : E ≤ (d.S : Subgroup d.H).map d.H.subtype)
    (he : ((MonoidHom.fst SymmetricFourWreath.P D).comp e.toMonoidHom).ker =
      E.subgroupOf ((d.S : Subgroup d.H).map d.H.subtype)) :
    let B := M ⊓ d.block.map d.H.subtype
    let K := (pResidual 2 B).map B.subtype
    (T : Subgroup G) ≤ normalizer ((K.pCoreIn 2 ⊔ E : Subgroup G) : Set G) := by
  let B := M ⊓ d.block.map d.H.subtype
  let K := (pResidual 2 B).map B.subtype
  let P := K.pCoreIn 2
  let R := (d.S : Subgroup d.H).map d.H.subtype
  obtain ⟨hPR,hRP⟩ := d.single_borel_core_placement hsingle
  let Q := P.subgroupOf R
  let eQ : Q ≃* P := subgroupOfEquivOfLe hPR
  let : Q.Normal := (normal_subgroupOf_iff_le_normalizer hPR).mpr hRP
  obtain ⟨hp⟩ := d.single_alternating_borel_core_quaternion hG T hST hsingle hA
  let hq := hp.map eQ.symm
  let : IsExtraspecial 2 Q := hq.extraspecial
  have hchar := SymmetricFourWreath.core_sup_factor_characteristic_of_equiv_prod e Q hq.card
  rw [he] at hchar
  let F := Q ⊔ E.subgroupOf R
  let : F.Characteristic := hchar
  have hi := (d.single_alternating_sylow_index_source hG T hM hTM hu hST hsingle hA).1
  let : (R.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hi
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hST.le).mp inferInstance
  have hh := hTR.trans (normalizer_le_normalizer_characteristic_image R F)
  change (T : Subgroup G) ≤ normalizer ((Q ⊔ E.subgroupOf R).map R.subtype : Set G) at hh
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hER] at hh
  have hQ : Q.map R.subtype = P := map_subgroupOf_eq_of_le hPR
  rwa [hQ] at hh

end CFSG.Quasithin.Chapter2
