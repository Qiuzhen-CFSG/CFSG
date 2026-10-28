module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.Borel
public import CFSG.Quasithin.Chapter10.SourceParabolicControl
/-!
# Odd Hall placement in the original local join gives Borel placement

An odd-order subgroup of the original local join lies in its two-residual,
whose ambient image is the original component orbit. H-star minimality then
places it in the original orbit Borel. This retains the literal Hall subgroup
used in the weak-closure upper bound.
Source: Aschbacher--Smith 10.2.3, printed pp.745--746.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}

theorem source_a5_hstar_hall_borel_of_localJoin
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup Subgroup.OddHall.oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hBJ : B.map H.subtype ≤ localJoin T L) : B.map H.subtype ≤ sourceOrbitBorel T L := by
  have hBodd : Odd (Nat.card (B.map H.subtype)) := by
    rw [card_map_of_injective H.subtype_injective]
    apply Nat.not_even_iff_odd.mp
    intro he
    apply hHall.p_in_pi_of_p_dvd_card ⟨2,Nat.prime_two⟩ _ rfl
    rw [Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv]
    exact even_iff_two_dvd.mp he
  have hBR : B.map H.subtype ≤ localOrbit T L := by
    rw [←source_join_residual D]
    intro b hb
    refine ⟨⟨b,hBJ hb⟩,mem_pResidual_of_orderOf_coprime ?_,rfl⟩
    have hd : orderOf (⟨b,hBJ hb⟩ : localJoin T L) ∣ Nat.card (B.map H.subtype) := by
      simpa only [Subgroup.orderOf_mk] using orderOf_dvd_natCard (⟨b,hb⟩ : B.map H.subtype)
    exact hBodd.coprime_two_left.coprime_dvd_right hd
  exact source_a5_hstar_odd_subgroup_le_borel_of_le_orbit D e hn hH
    (B.map H.subtype) (map_subtype_le B) hBR hBodd
end CFSG.Quasithin.Chapter10
