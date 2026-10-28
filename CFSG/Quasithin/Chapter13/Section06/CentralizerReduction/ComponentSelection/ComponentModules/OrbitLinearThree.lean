module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitCoordinates
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitComparison
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitCubic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.LinearThree.OrbitCoordinates.Quotient
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.LinearThree.ProductCalculation
/-!
# The cubic diagonal obstruction to the linear-three orbit

Restrict the original local C-component to its two-conjugate span. The
moving Sylow element supplies an automorphism exchanging the factors,
while the Sylow intersection preserves L_v. The intrinsic quotient product
calculation makes the three-part of its image a square, contradicting the
original cubic two-core quotient. Thus the complete model comparison leaves
an actual SL₂ model over a binary field of order at least four.

The earlier-source containment L_v ≤ K₋ remains explicit. No model or
representation decomposition is assumed. Its discharge belongs to the
1.2.2 source application; the original consumer below isolates that remaining
containment from the completed model comparison and diagonal calculation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.14, printed p.929, using the intrinsic binary PSL₃ Sylow calculation.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel.LinearThree
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Product coordinates for the actual exchanged orbit, preserving L_v. -/
theorem orbit_linearThree_coordinates
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G))
    (hLv : Lv L v ≤ Kminus K T v)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2) :
    Nonempty (ProductCoordinates (K.subgroupOf (Kminus K T v))
      ((Lv L v).subgroupOf (Kminus K T v))) := by
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
  have hfixY : ((Lv L v).subgroupOf H).map a.toMonoidHom = (Lv L v).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hmap, map_subgroupOf_eq_of_le hLv]
    exact mem_normalizer_iff_map_conj_eq.mp (hL ht)
  have hnorm : (H.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hJH
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    hK.1.2.2.1 hHJ hnorm.isSubnormal
  have hSY : (S : Subgroup H) ≤ normalizer ((Lv L v).subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hLv]
    intro s hs
    have hsT : (s : G) ∈ Tv T v ⊓ H := hS ▸ mem_map_of_mem H.subtype hs
    exact hL hsT.1
  let eB : B ≃* K := subgroupOfEquivOfLe hKH
  have hmB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 2 :=
    hm.of_mulEquiv (QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB))
  exact OrbitCoordinates.of_component_pair B ((Lv L v).subgroupOf H) hB hmB a hne hgen hswapB hfixY S hSY

private theorem cubic_core_sylow_card {D : Type*} [Group D] [Finite D]
    (hc : Nat.card (D ⧸ pCore 2 D) = 3) (P : Sylow 3 D) : Nat.card P = 3 := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := D)).exists_card_eq
  have hsize : Nat.card D = 3 * 2 ^ n := by
    rw [← (pCore 2 D).index_mul_card, index_eq_card, hc, hn]
  have hd : 3 ∣ Nat.card D := by rw [hsize]; exact dvd_mul_right _ _
  apply Nat.dvd_antisymm ?_ (P.dvd_card_of_dvd_card hd)
  have hcop : (Nat.card P).Coprime (2 ^ n) := by
    obtain ⟨r, hr⟩ := P.isPGroup'.exists_card_eq
    rw [hr]
    exact (by decide : Nat.Coprime 3 2).pow r n
  apply hcop.dvd_of_dvd_mul_right
  rw [← hsize]
  exact (P : Subgroup D).card_subgroup_dvd_card

/-- The original cubic quotient excludes the linear-three orbit. -/
theorem orbit_linearThree_excluded_source
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G))
    (hLv : Lv L v ≤ Kminus K T v)
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2) : False := by
  obtain ⟨a⟩ := orbit_linearThree_coordinates K L T z v hlocal hL hK hn hLv hm
  exact ProductCalculation.not_sylow_three_card_eq_three a.firstSylow a.secondSylow
    (model_sylow_self_normalizing a.firstModel a.firstSylow)
    (model_sylow_self_normalizing a.secondModel a.secondSylow)
    _ a.sylow_invariant a.exchange a.exchange_first a.exchange_second a.exchange_invariant
    (sylow_three_card_image a.quotient a.kernel_two _
      (sylow_three_card_subgroupOf _ _ hLv (cubic_core_sylow_card hc)))

open A5Module ComponentReduction InitialSieve
open scoped MatrixGroups
variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- After the source residual containment, the original comparison leaves
an actual SL₂ model over a binary field of order at least four. -/
theorem noninvariant_component_linearTwo_original_source
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
    (hLv : Lv L (markedV d.flag.module) ≤ Kminus K (T : Subgroup G) (markedV d.flag.module)) :
    ∃ F : ChapterB.QuasisimpleSource.BinaryField,
      4 ≤ Nat.card F.Carrier ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* SL(2,F.Carrier)) ∧
      Nonempty (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz K ≃* SL(2,F.Carrier)) := by
  rcases noninvariant_component_models_original_source d V₃ earlier hG hm hcounter hfusion
    K hK hn hL hz with he | he
  · exact he
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier hcounter hfusion
  exact (orbit_linearThree_excluded_source K L (T : Subgroup G) _ _
    (hG.involution_centralizer_sqtk (marked_orders d.flag.module).2) hL hK hn hLv
    c.residual_card he.1).elim

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
