module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitLinearThree
/-!
# The cubic diagonal exclusion using only plus placement

Pull the actual L_v plus image back through the restriction of the plus map
to K₋. Its kernel is a two-group because it restricts the proved join map.
Consequently this original-subgroup preimage has Sylow three-order three,
and T_v normalizes it. The actual exchanged component coordinates and the
intrinsic product obstruction then exclude PSL₃(2). No lifting of L_v itself
into K₋ is required. The original model consumer uses precisely the plus
containment furnished by the source 1.2.2 application.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.14, printed p.929.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel.LinearThree
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The exchanged orbit retains any actual Sylow-invariant subgroup. -/
theorem orbit_linearThree_coordinates_of_invariant_subgroup
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G))
    (Y : Subgroup G) (hY : Y ≤ Kminus K T v)
    (hTY : Tv T v ≤ normalizer (Y : Set G))
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2) :
    Nonempty (ProductCoordinates (K.subgroupOf (Kminus K T v))
      ((Y).subgroupOf (Kminus K T v))) := by
  obtain ⟨hi, _, t, ht, htN, hp⟩ :=
    noninvariant_component_pair_source K L T z v hlocal hK hn
  let H := Kminus K T v
  let J := K ⊔ Tv T v
  have hKJ : K ≤ J := le_sup_left
  have hTJ : Tv T v ≤ J := le_sup_right
  have hKH : K ≤ H := le_conjugateSpanBy K (Tv T v)
  have hHJ : H ≤ J := conjugateSpanBy_le hKJ (hTJ.trans J.le_normalizer)
  have hJH : J ≤ normalizer (H : Set G) :=
    sup_le (hKH.trans H.le_normalizer) (le_normalizer_conjugateSpanBy K (Tv T v))
  have htH : H.conjBy t = H :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy K (Tv T v) ht)
  let a : MulAut H := ((MulAut.conj t).subgroupMap H).trans (MulEquiv.subgroupCongr htH)
  have ha : H.subtype.comp a.toMonoidHom = (MulAut.conj t).toMonoidHom.comp H.subtype := by
    ext x
    rfl
  have hmap (D : Subgroup H) : (D.map a.toMonoidHom).map H.subtype =
      (D.map H.subtype).conjBy t := by
    rw [map_map, ha, ← map_map]
    rfl
  let B := K.subgroupOf H
  have hBK : B.map H.subtype = K := map_subgroupOf_eq_of_le hKH
  have hB : B.IsCComponent := hK.1.2.1.subgroupOf_of_le hKH hHJ
  have hne : B ≠ B.map a.toMonoidHom := by
    intro he
    have hh := congrArg (Subgroup.map H.subtype) he
    rw [hmap, hBK] at hh
    exact htN (mem_normalizer_iff_map_conj_eq.mpr hh.symm)
  have hgen : B ⊔ B.map a.toMonoidHom = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, hmap, hBK, ← hp, ← MonoidHom.range_eq_map, range_subtype]
  have hswap : (K.conjBy t).conjBy t = K := by
    have ht2 : t * t ∈ normalizer (K : Set G) := by
      let tJ : J := ⟨t, hTJ ht⟩
      have hh : tJ * tJ ∈ normalizer (K.subgroupOf J : Set J) :=
        (mul_mem_iff_of_index_two hi).mpr Iff.rfl
      rw [← subgroupOf_normalizer_eq hKJ] at hh
      exact hh
    rw [← conjBy_mul]
    exact mem_normalizer_iff_map_conj_eq.mp ht2
  have hswapB : (B.map a.toMonoidHom).map a.toMonoidHom = B := by
    apply map_injective H.subtype_injective
    rw [hmap, hmap, hBK, hswap]
  have hfixY : ((Y).subgroupOf H).map a.toMonoidHom = (Y).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hmap, map_subgroupOf_eq_of_le hY]
    exact mem_normalizer_iff_map_conj_eq.mp (hTY ht)
  have hnorm : (H.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hJH
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    hK.1.2.2.1 hHJ hnorm.isSubnormal
  have hSY : (S : Subgroup H) ≤ normalizer ((Y).subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hY]
    intro s hs
    have hsT : (s : G) ∈ Tv T v ⊓ H := hS ▸ mem_map_of_mem H.subtype hs
    exact hTY hsT.1
  let eB : B ≃* K := subgroupOfEquivOfLe hKH
  have hmB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 2 :=
    hm.of_mulEquiv (QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB))
  exact OrbitCoordinates.of_component_pair B ((Y).subgroupOf H) hB hmB a hne hgen hswapB hfixY S hSY

private theorem sylow_three_card_transport {D E : Type*} [Group D] [Finite D] [Group E]
    (e : D ≃* E) (h : ∀ P : Sylow 3 E, Nat.card P = 3) (P : Sylow 3 D) : Nat.card P = 3 := by
  have hh := h (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  change Nat.card ((P : Subgroup D).map e.toMonoidHom) = 3 at hh
  rwa [card_map_of_injective e.injective] at hh

private theorem sylow_three_card_of_image {D E : Type*} [Group D] [Finite D] [Group E]
    (f : D →* E) (hk : IsPGroup 2 f.ker) (Y : Subgroup D)
    (hY : ∀ P : Sylow 3 (Y.map f), Nat.card P = 3) (P : Sylow 3 Y) : Nat.card P = 3 := by
  let g := f.subgroupMap Y
  have hg : Function.Surjective g := f.subgroupMap_surjective Y
  have hkg : IsPGroup 2 g.ker := by
    dsimp [g]
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  have hcop : Nat.Coprime 3 (Nat.card g.ker) := by
    obtain ⟨n,hn⟩ := hkg.exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn
  let Q := P.mapSurjective hg
  exact (Nat.card_congr (P.equivOfSurjectiveCoprime g hg hcop Q).toEquiv).trans (hY Q)

/-- Cubic plus placement suffices to exclude the linear-three orbit. -/
theorem orbit_linearThree_excluded_of_plus_placement
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G))
    (hLvplus : plusImage K L T z v hL hz (Lv L v) ≤
      plusImage K L T z v hL hz (Kminus K T v))
    (hthree : ∀ P : Sylow 3 (plusImage K L T z v hL hz (Lv L v)), Nat.card P = 3)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2) : False := by
  let H := Kminus K T v
  have hHA : H ≤ plusActor K L T v := le_sup_left.trans le_sup_left
  have hHJ : H ≤ K ⊔ Tv T v :=
    conjugateSpanBy_le le_sup_left (le_sup_right.trans (K ⊔ Tv T v).le_normalizer)
  let q : H →* Gplus K L T z v hL hz :=
    (plusMk K L T z v hL hz).comp (inclusion hHA)
  have hqj : q = (joinPlusMap K L T z v hL hz).comp (inclusion hHJ) := rfl
  have hq2 : IsPGroup 2 q.ker := by
    change IsPGroup 2 ((joinPlusMap K L T z v hL hz).ker.comap (inclusion hHJ))
    exact (joinPlusMap_ker_isTwoGroup_source K L T z v hlocal hL hz hK hn).comap_of_injective
      (inclusion hHJ) (inclusion_injective hHJ)
  let W := plusImage K L T z v hL hz (Lv L v)
  let YH := W.comap q
  let Y := YH.map H.subtype
  have hYH : Y ≤ H := map_subtype_le _
  have hqrange : q.range = plusImage K L T z v hL hz H := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨inclusion hHA a,a.property,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩
  have hYmap : YH.map q = W := by
    rw [map_comap_eq,hqrange]
    exact inf_eq_right.mpr hLvplus
  have hTY : Tv T v ≤ normalizer (Y : Set G) := by
    apply le_normalizer_iff.mpr
    intro t ht y hy
    obtain ⟨x,hx,rfl⟩ := hy
    have htH := le_normalizer_conjugateSpanBy K (Tv T v) ht
    let tA : plusActor K L T v := ⟨t,(show Tv T v ≤ plusActor K L T v from le_sup_right) ht⟩
    have htW : plusMk K L T z v hL hz tA ∈ normalizer (W : Set _) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      have he := plusImage_conjBy_source K L T (Lv L v) z v hL hz
        (le_sup_right.trans le_sup_left) tA
      have hLt : (Lv L v).conjBy t = Lv L v := mem_normalizer_iff_map_conj_eq.mp (hL ht)
      change plusImage K L T z v hL hz ((Lv L v).conjBy t) = _ at he
      rw [hLt] at he
      exact he.symm
    let y : H := ⟨t * x * t⁻¹,(mem_normalizer_iff.mp htH x).mp x.property⟩
    refine ⟨y,?_,rfl⟩
    change q y ∈ W
    have he : q y = plusMk K L T z v hL hz tA * q x *
        (plusMk K L T z v hL hz tA)⁻¹ := by
      change plusMk K L T z v hL hz (tA * inclusion hHA x * tA⁻¹) = _
      rw [map_mul,map_mul,map_inv]
      rfl
    rw [he]
    exact (mem_normalizer_iff.mp htW (q x)).mp hx
  have hYthree : ∀ P : Sylow 3 Y, Nat.card P = 3 := by
    apply sylow_three_card_transport (YH.equivMapOfInjective H.subtype H.subtype_injective).symm
    exact sylow_three_card_of_image q hq2 YH
      (sylow_three_card_transport (MulEquiv.subgroupCongr hYmap) hthree)
  obtain ⟨a⟩ := orbit_linearThree_coordinates_of_invariant_subgroup K L T z v hlocal
    hK hn Y hYH hTY hm
  exact ProductCalculation.not_sylow_three_card_eq_three a.firstSylow a.secondSylow
    (model_sylow_self_normalizing a.firstModel a.firstSylow)
    (model_sylow_self_normalizing a.secondModel a.secondSylow)
    _ a.sylow_invariant a.exchange a.exchange_first a.exchange_second a.exchange_invariant
    (sylow_three_card_image a.quotient a.kernel_two _
      (sylow_three_card_subgroupOf _ _ hYH hYthree))

open A5Module ComponentReduction InitialSieve
open scoped MatrixGroups
variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- The source group model needs only containment of the residual in the
actual plus pair, not containment before quotienting. -/
theorem noninvariant_component_linearTwo_of_plus_placement_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (K : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : ¬ Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (hLvplus : plusImage K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz
        (Lv L (markedV d.flag.module)) ≤
      plusImage K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz
        (Kminus K (T : Subgroup G) (markedV d.flag.module))) :
    ∃ F : ChapterB.QuasisimpleSource.BinaryField,
      4 ≤ Nat.card F.Carrier ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* SL(2,F.Carrier)) ∧
      Nonempty (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz K ≃* SL(2,F.Carrier)) := by
  rcases noninvariant_component_models_original_source d V₃ earlier hG hm hcounter hfusion
    K hK hn hL hz with he | he
  · exact he
  exact (orbit_linearThree_excluded_of_plus_placement K L (T : Subgroup G) _ _
    (hG.involution_centralizer_sqtk (marked_orders d.flag.module).2) hL hz hK hn hLvplus
    (plusLv_sylow_three_card_original_source d V₃ earlier hcounter hfusion K hL hz) he.1).elim

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
