module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ExchangedActors
public import Theory.SpecificGroups.PSL2.SixteenWreathOrder
public import Theory.GroupTheory.SylowSubnormalIntersectionIndex

/-!
# Full Sylow-five intersections in the exchanged source branch

The actual Aut(PSL₂(16)) wreath quotient has five-part 25. The original
factor-join index gives |H/O₂(H)| = 200, so H has index prime to five
inside Mc. Its intersection with each subnormal component therefore has
order divisible by five. The previously constructed Borel torus embedding
bounds its two-core quotient by five, proving equality. Transport through
the literal quotient map gives order five for each component actor image.

The last theorem constructs both actors from the original Context. Their
alignment with the earlier dihedral factors and the remaining module
geometry stay with qt-e-14615-quintic-exclusion. The original 14.6.12
factor-join index remains an allowed earlier-source premise, whose
producer is qt-e-14612-singleton; final suitable-choice assembly must
discharge it and the original 14.6.13--14 inputs.
Source: Aschbacher--Smith 14.6.15, printed pp.1033--1034.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ComponentExclusion
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)

include s in
private theorem original_H_le_partner : H ≤ Mc := by
  have he := (Section02.source_lemma_14_2_3 s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action H s.outside.1 s.outside.2).1
  exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2

include s in
theorem source_exchanged_outside_index_primeTo_five : ¬5 ∣ H.relIndex Mc := by
  obtain ⟨e⟩ := (source_exchanged_closure_model s).2
  have hnc : ¬125 ∣ Nat.card Mc := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := Mc)).exists_card_eq
    intro hd
    rw [←(pCore 2 Mc).card_mul_index,index_eq_card,hn,
      Nat.card_congr e.toEquiv] at hd
    exact Theory.PSL2.SixteenWreathComponents.not_five_cube_dvd_card
      (((by decide : Nat.Coprime 125 2).pow_right n).dvd_of_dvd_mul_left hd)
  have h25 : 25 ∣ Nat.card (H.subgroupOf Mc) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (original_H_le_partner s)).toEquiv]
    have hd := card_quotient_dvd_card (pCore 2 H)
    rw [OddCriticalPair.exchanged_actor_card a (T : Subgroup G) 5 H0 H1 H2 s.factors] at hd
    exact (by decide : 25 ∣ 8 * 5 ^ 2).trans hd
  intro hi
  change 5 ∣ (H.subgroupOf Mc).index at hi
  apply hnc
  have hd := Nat.mul_dvd_mul h25 hi
  rwa [(H.subgroupOf Mc).card_mul_index] at hd

include s in
theorem source_exchanged_intersection_five_dvd {K : Subgroup G}
    (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (em : Nonempty ((K ⧸ pCore 2 K) ≃* Theory.PSL2.SixteenWreathComponents.L)) :
    5 ∣ Nat.card (K ⊓ H : Subgroup G) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hd : 5 ∣ Nat.card (K.subgroupOf Mc) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hKM).toEquiv]
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 K))
    rw [Nat.card_congr em.some.toEquiv]
    exact Theory.PSL2.SixteenWreathComponents.five_dvd_card
  have hh := prime_dvd_intersection_of_subnormal_of_primeTo_index
    (H.subgroupOf Mc) (K.subgroupOf Mc)
    (source_exchanged_outside_index_primeTo_five s) hK.subnormal hd
  have he : ((K.subgroupOf Mc) ⊓ (H.subgroupOf Mc)).map Mc.subtype = K ⊓ H := by
    rw [Subgroup.map_inf _ _ _ Mc.subtype_injective,
      map_subgroupOf_eq_of_le hKM,map_subgroupOf_eq_of_le (original_H_le_partner s)]
  rwa [←he,card_map_of_injective Mc.subtype_injective]

include s in
theorem source_exchanged_intersection_quotient_card {K : Subgroup G}
    (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (em : Nonempty ((K ⧸ pCore 2 K) ≃* Theory.PSL2.SixteenWreathComponents.L)) :
    Nat.card ((K ⊓ H : Subgroup G) ⧸ pCore 2 (K ⊓ H : Subgroup G)) = 5 := by
  let B := K ⊓ H
  have hd := source_exchanged_intersection_five_dvd s hKM hK em
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
  change 5 ∣ Nat.card B at hd
  rw [←(pCore 2 B).card_mul_index,index_eq_card,hn] at hd
  exact Nat.dvd_antisymm
    (source_exchanged_intersection_quotient_card_dvd_five s hKM hK em)
    (((by decide : Nat.Coprime 5 2).pow_right n).dvd_of_dvd_mul_left hd)

include s in
theorem source_exchanged_component_actor_card
    (b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T))
    {K : Subgroup G} (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (em : Nonempty ((K ⧸ pCore 2 K) ≃* Theory.PSL2.SixteenWreathComponents.L))
    (hKz : K ≤ residualClosure H Mc) : Nat.card (actorImage H K) = 5 := by
  obtain ⟨e,_⟩ := source_exchanged_component_actor_quotient s b hKM hK em hKz
  rw [←Nat.card_congr e.toEquiv]
  exact source_exchanged_intersection_quotient_card s hKM hK em

include s in
theorem source_exchanged_actor_cardinalities :
    ∃ b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T),
      Nat.card (actorImage H b.K1) = 5 ∧ Nat.card (actorImage H b.K2) = 5 := by
  obtain ⟨b⟩ := source_exchanged_factor_data s
  exact ⟨b,source_exchanged_component_actor_card s b b.first_le b.first_component b.first_model
    ((le_sup_left : b.K1 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq),
    source_exchanged_component_actor_card s b b.second_le b.second_component b.second_model
    ((le_sup_right : b.K2 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq)⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
