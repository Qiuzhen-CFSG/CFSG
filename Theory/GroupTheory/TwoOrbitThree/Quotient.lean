module
public import Theory.GroupTheory.TwoOrbitThree.Normalizer
public import GorensteinWalter.PSL2Center
/-!
# Two conjugate C-components through the actual two-core quotient

The canonical quotient maps identify each component core quotient with its
image. An index-two component normalizer remains index two in that quotient,
and the distinct ordinary components there commute. The two concrete outer
calculations prove three-prime index for their product. Multiplying by the
relative two-core index lifts this conclusion to the original component join.
Source: Aschbacher--Smith 1.2.2(a), printed p.504, 1 March 2004.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace Theory.GroupTheory.TwoOrbitThree
variable {G : Type*} [Group G] [Finite G]

private theorem center_bot_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center A = ⊥) : center B = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have h : e.symm x ∈ center A := ((centerCongr e).symm ⟨x,hx⟩).property
  have he : e.symm x = 1 := by simpa only [hz,mem_bot] using h
  exact e.symm.map_eq_one_iff.mp he

omit [Finite G] in
theorem pair_map_quotient (L : Subgroup G) (t : G) (Q : Subgroup G) [Q.Normal] :
    (L ⊔ L.conjBy t).map (QuotientGroup.mk' Q) =
      L.map (QuotientGroup.mk' Q) ⊔ (L.map (QuotientGroup.mk' Q)).conjBy (QuotientGroup.mk' Q t) := by
  rw [Subgroup.map_sup]
  congr 1
  change (L.map (MulAut.conj t).toMonoidHom).map (QuotientGroup.mk' Q) =
    (L.map (QuotientGroup.mk' Q)).map (MulAut.conj (QuotientGroup.mk' Q t)).toMonoidHom
  rw [map_map,map_map]
  congr 1

theorem pair_index_coprime_of_quotient_pair (L : Subgroup G) (t : G) [(L ⊔ L.conjBy t).Normal]
    (hindex : Nat.Coprime 3 (L.map (QuotientGroup.mk' (pCore 2 G)) ⊔
      (L.map (QuotientGroup.mk' (pCore 2 G))).conjBy (QuotientGroup.mk' (pCore 2 G) t)).index) :
    Nat.Coprime 3 (L ⊔ L.conjBy t).index := by
  rw [←pair_map_quotient L t,index_map,QuotientGroup.ker_mk',
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),index_top,mul_one] at hindex
  have hcore : Nat.Coprime 3 (Nat.card (pCore 2 G)) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn
  rw [←relIndex_mul_index (show L ⊔ L.conjBy t ≤ L ⊔ L.conjBy t ⊔ pCore 2 G from le_sup_left)]
  apply Nat.Coprime.mul_right _ hindex
  rw [relIndex_sup_left]
  exact hcore.coprime_dvd_right (relIndex_dvd_card _ _)

theorem quotient_pair_commutes {L : Subgroup G} (hL : L.IsCComponent)
    [IsQuasisimple (L ⧸ pCore 2 L)] (t : G) (ht : t ∉ normalizer (L : Set G)) :
    ⁅L.map (QuotientGroup.mk' (pCore 2 G)),
      (L.map (QuotientGroup.mk' (pCore 2 G))).conjBy (QuotientGroup.mk' (pCore 2 G) t)⁆ = ⊥ := by
  let _ := pCore_isNilpotent (p := 2) (G := G)
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := L.map q
  let e := cComponentTwoCoreQuotientEquiv hL
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e
  have hc : IsComponent (G ⧸ pCore 2 G) B := ⟨(hL.map_quotient _).subnormal,inferInstance⟩
  exact hc.commutator_eq_bot_of_ne (hc.map_conj (q t)) (fun he => ht (by
    have hh : q t ∈ normalizer (B : Set (G ⧸ pCore 2 G)) :=
      mem_normalizer_iff_map_conj_eq.mpr he.symm
    have hp : t ∈ (normalizer (L.map q)).comap q := hh
    rwa [normalizer_cComponent_quotient hL (pCore 2 G)] at hp))

theorem binary_cComponent_pair_index_coprime_three
    {L : Subgroup G} (hL : L.IsCComponent) [IsQuasisimple (L ⧸ pCore 2 L)]
    (hi : (normalizer (L : Set G)).index = 2) (t : G) (ht : t ∉ normalizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L)) (hr : primeRank 3 G ≤ 2)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group F) :
    Nat.Coprime 3 (L ⊔ L.conjBy t).index := by
  let _ := pCore_isNilpotent (p := 2) (G := G)
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := L.map q
  let eB := cComponentTwoCoreQuotientEquiv hL
  let : (L ⊔ L.conjBy t).Normal := pair_normal_of_index_two L hi t ht
  apply pair_index_coprime_of_quotient_pair L t
  apply binary_pair_index_coprime_three B
    ((cComponent_normalizer_index_quotient hL _).trans hi) (q t)
    (quotient_pair_commutes hL t ht)
    (center_bot_transport (eB.symm.trans e).symm (GorensteinWalter.psl2_center_eq_bot F))
    (by rwa [←Nat.card_congr eB.toEquiv])
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hr)
    F (eB.symm.trans e)

theorem outer_cComponent_pair_index_coprime_three
    {L : Subgroup G} (hL : L.IsCComponent) [IsQuasisimple (L ⧸ pCore 2 L)]
    (hi : (normalizer (L : Set G)).index = 2) (t : G) (ht : t ∉ normalizer (L : Set G))
    (hz : center (L ⧸ pCore 2 L) = ⊥)
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L)) (hr : primeRank 3 G ≤ 2)
    (ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (L ⧸ pCore 2 L)))) :
    Nat.Coprime 3 (L ⊔ L.conjBy t).index := by
  let _ := pCore_isNilpotent (p := 2) (G := G)
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := L.map q
  let eB := cComponentTwoCoreQuotientEquiv hL
  let : (L ⊔ L.conjBy t).Normal := pair_normal_of_index_two L hi t ht
  apply pair_index_coprime_of_quotient_pair L t
  apply outer_pair_index_coprime_three B
    ((cComponent_normalizer_index_quotient hL _).trans hi) (q t)
    (quotient_pair_commutes hL t ht) (center_bot_transport eB hz)
    (by rwa [←Nat.card_congr eB.toEquiv])
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hr)
  change Nat.Coprime 3 (Nat.card (MulAut.Outer B))
  rwa [←Nat.card_congr (MulAut.outerCongr eB).toEquiv]

end Theory.GroupTheory.TwoOrbitThree
