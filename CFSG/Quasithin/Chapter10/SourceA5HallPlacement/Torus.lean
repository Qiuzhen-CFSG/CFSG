module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.Borel
public import Theory.Alternating.FivePairBorelTorus

/-!
# The actual containing Hall torus in the natural A₅ branch

An odd subgroup of an HStar intersection that acts faithfully on the original
A₅-pair section lies in the two-residual of the original Sylow normalizer.
A Sylow three-subgroup of that normalizer gives a containing odd Hall subgroup
of the residual, of order nine and exponent three. All subgroups are retained
inside G, including the full two-core of the normalizer and its residual.

Source: Aschbacher–Smith 10.2.3, printed pp.745–746, specialized to n = 2.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter4
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
include D e

omit e in
private theorem orbit_sylow_intersection :
    ∃ S : Sylow 2 (localOrbit T L),
      (S : Subgroup (localOrbit T L)) = (T : Subgroup G).subgroupOf (localOrbit T L) := by
  let R := localOrbit T L
  let M := D.maximalLocal
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨P,hP⟩ := (T.subtype (le_normalizer_componentOrbit L T)).exists_subgroupOf_eq_of_normal
    (R.subgroupOf M)
  let a := subgroupOfEquivOfLe R.le_normalizer
  refine ⟨P.mapSurjective (f := a.toMonoidHom) a.surjective,?_⟩
  change (P : Subgroup (R.subgroupOf M)).map a.toMonoidHom = _
  rw [hP]
  ext r
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx
  · intro hr
    exact ⟨⟨⟨r,R.le_normalizer r.property⟩,r.property⟩,hr,rfl⟩

omit D e [Finite G] in
private theorem relative_hall_restrict (C K N : Subgroup G) (hCK : C ≤ K) (hKN : K ≤ N)
    (h : IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} (C.subgroupOf N)) :
    IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} (C.subgroupOf K) := by
  have hCN := hCK.trans hKN
  have hc : Nat.card (C.subgroupOf K) = Nat.card (C.subgroupOf N) :=
    (Nat.card_congr (subgroupOfEquivOfLe hCK).toEquiv).trans
      (Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv).symm
  have hi : (C.subgroupOf K).index ∣ (C.subgroupOf N).index := by
    have hh := (C.subgroupOf N).relIndex_dvd_index_of_le
      (show C.subgroupOf N ≤ K.subgroupOf N from fun _ hx => hCK hx)
    rwa [relIndex_subgroupOf hKN] at hh
  exact ⟨fun p hp => h.p_in_pi_of_p_dvd_card p (hc ▸ hp),
    fun p hp => h.p_in_pi_of_p_dvd_index p (hp.trans hi)⟩

theorem source_a5_exists_hall_torus_of_borel_placement
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hB : IsPGroup 3 B) (hBB : B ≤ sourceOrbitBorel T L) :
    ∃ C : Subgroup G, B ≤ C ∧ C ≤ sourceOrbitBorel T L ∧
      IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} (C.subgroupOf (sourceOrbitBorel T L)) ∧
      Nat.card C = 9 ∧ IsElementaryAbelian 3 C := by
  let R := localOrbit T L
  let N := sourceOrbitSylowNormalizer T L
  let B0 := sourceOrbitBorel T L
  have hB0N : B0 ≤ N := map_subtype_le _
  have hNR : N ≤ R := inf_le_left
  have hBR : B ≤ R := hBB.trans (hB0N.trans hNR)
  obtain ⟨S,hS⟩ := orbit_sylow_intersection D
  let NR := normalizer (S : Set R)
  have hNsub : N.subgroupOf R = NR := by
    change (R ⊓ normalizer ((T : Subgroup G) ⊓ R : Set G)).subgroupOf R = _
    rw [inf_subgroupOf_left]
    change (normalizer (((T : Subgroup G) ⊓ R : Subgroup G) : Set G)).subgroupOf R = NR
    rw [subgroupOf_normalizer_eq (show (T : Subgroup G) ⊓ R ≤ R from inf_le_right)]
    have hh : ((T : Subgroup G) ⊓ R).subgroupOf R = (T : Subgroup G).subgroupOf R := by
      ext x
      exact ⟨fun h => h.1,fun h => ⟨h,x.property⟩⟩
    rw [hh,←hS]
    rfl
  have hNmap : NR.map R.subtype = N := by
    rw [←hNsub,map_subgroupOf_eq_of_le hNR]
  have hBNR : B.subgroupOf R ≤ NR := by
    rw [←hNsub]
    exact fun _ hx => (hBB.trans hB0N) hx
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp hn
  obtain ⟨q,hq,hk,_⟩ := source_a5_original_product_quotient D e hn ht htn
  have hqk : IsPGroup 2 q.ker := hk ▸ pCore_isPGroup
  obtain ⟨C0,hBC,hC0N,hHall,hC0c,hC0e⟩ :=
    Theory.AlternatingFive.exists_three_torus_in_sylow_normalizer q hq hqk S
      (B.subgroupOf R) hB.comap_subtype hBNR
  let C := C0.map R.subtype
  have hCN : C ≤ N := (map_mono hC0N).trans_eq hNmap
  have hCc : Nat.card C = 9 := by
    rw [card_map_of_injective R.subtype_injective]
    exact hC0c
  let := hC0e
  have hCe : IsElementaryAbelian 3 C := IsElementaryAbelian.map_subtype
  have hCB0 : C ≤ B0 := by
    intro c hc
    refine ⟨⟨c,hCN hc⟩,mem_pResidual_of_orderOf_coprime ?_,rfl⟩
    have ho : orderOf (⟨c,hCN hc⟩ : N) ∣ 9 := by
      have hh := orderOf_dvd_natCard (⟨c,hc⟩ : C)
      simpa only [Subgroup.orderOf_mk,hCc] using hh
    exact (by decide : Nat.Coprime 2 9).coprime_dvd_right ho
  let a : NR ≃* N := (NR.equivMapOfInjective R.subtype R.subtype_injective).trans
    (MulEquiv.subgroupCongr hNmap)
  have hmapC : (C0.subgroupOf NR).map a.toMonoidHom = C.subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [map_map,show N.subtype.comp a.toMonoidHom = R.subtype.comp NR.subtype from rfl,
      ←map_map,map_subgroupOf_eq_of_le hC0N,map_subgroupOf_eq_of_le hCN]
  have hHallN : IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} (C.subgroupOf N) := by
    rw [← hmapC]
    refine ⟨?_,?_⟩
    · intro p hp
      rw [card_map_of_injective a.injective] at hp
      exact hHall.p_in_pi_of_p_dvd_card p hp
    · intro p hp
      have hi := index_map_of_bijective (f := a.toMonoidHom) a.bijective (C0.subgroupOf NR)
      rw [hi] at hp
      exact hHall.p_in_pi_of_p_dvd_index p hp
  refine ⟨C,?_,hCB0,relative_hall_restrict C B0 N hCB0 hB0N hHallN,hCc,hCe⟩
  intro b hb
  exact ⟨⟨b,hBR hb⟩,hBC hb,rfl⟩

theorem source_a5_hstar_faithful_odd_subgroup_hall_torus
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup G) (hBH : B ≤ H) (hBM : B ≤ D.maximalLocal)
    (hodd : Odd (Nat.card B))
    (hfaith : B ⊓ sectionCentralizer (localOrbit T L) = ⊥) :
    ∃ C : Subgroup G, B ≤ C ∧ C ≤ sourceOrbitBorel T L ∧
      IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} (C.subgroupOf (sourceOrbitBorel T L)) ∧
      Nat.card C = 9 ∧ IsElementaryAbelian 3 C := by
  have hBR := source_a5_faithful_odd_subgroup_le_orbit D e hn B hBM hodd hfaith
  exact source_a5_exists_hall_torus_of_borel_placement D e hn B
    (source_a5_hstar_odd_subgroup_isThreeGroup D e hn hH B hBH (hBR.trans le_sup_left) hodd)
    (source_a5_hstar_odd_subgroup_le_borel_of_le_orbit D e hn hH B hBH hBR hodd)

end CFSG.Quasithin.Chapter10
