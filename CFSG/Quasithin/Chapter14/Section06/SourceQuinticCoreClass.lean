module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticCoreLayers

/-!
# Class and exponent of the full original quintic core

The exact third commutator is the original central line, so the full core
has class three. Its Frattini subgroup is the elementary quintic span;
therefore every square has order at most two. Nonabelianness makes the
exponent exactly four. Both conclusions apply to the order-512 and
order-1024 possibilities without a core-order hypothesis.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The entire original quintic core has class three and exponent four,
with no restriction to the smaller local branch. -/
theorem source_quintic_full_core_class_and_exponent
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    Group.nilpotencyClass (H.pCoreIn 2) = 3 ∧
      Monoid.exponent (H.pCoreIn 2) = 4 := by
  let Q := H.pCoreIn 2
  let U := conjugateSpanBy (localModule T M) H
  let Z := centralInvolutions T
  let : Group.IsNilpotent Q := (isPGroup_pCoreIn 2 H).isNilpotent
  let : Fact (IsPGroup 2 Q) := ⟨isPGroup_pCoreIn 2 H⟩
  let : IsElementaryAbelian 2 U :=
    (Section02.SolvableAmalgam.source_index_five_closure_structure
      hG T hempty hM hu hmany hcard e H hH.1 hi).1
  obtain ⟨_, hPhi, hthird⟩ := source_quintic_full_core_layers
    hG T hempty hM hu hmany hcard e H hH hi
  have hHZ : H ≤ centralizer (Z : Set G) :=
    (Section02.source_lemma_14_2_3
      hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hfourth : ⁅⁅⁅Q,Q⁆,Q⁆,Q⁆ = ⊥ := by
    rw [hthird]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp ((pCoreIn_le 2 H).trans hHZ))
  have hL3 : (⊤ : Subgroup Q).lowerCentralSeries 3 = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ (f := Q.subtype) Q.subtype_injective).mp
    rw [map_lowerCentralSeries, ← MonoidHom.range_eq_map, range_subtype]
    exact hfourth
  have hc : Group.nilpotencyClass Q = 3 := by
    have hle := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hL3
    have hlo : ¬ Group.nilpotencyClass Q ≤ 2 := by
      intro hh
      have hL2 : (⊤ : Subgroup Q).lowerCentralSeries 2 = ⊥ :=
        Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hh
      have hm := congrArg (fun D : Subgroup Q => D.map Q.subtype) hL2
      rw [map_lowerCentralSeries, ← MonoidHom.range_eq_map, range_subtype,
        Subgroup.map_bot] at hm
      change ⁅⁅Q,Q⁆,Q⁆ = ⊥ at hm
      rw [hthird] at hm
      have hZ := plane_centralInvolutions_card T M hM.1.2 hcard e
      rw [hm, card_bot] at hZ
      omega
    omega
  have hexp : Monoid.exponent Q ∣ 4 := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro q
    have hsq : (q : G) ^ 2 ∈ U := hPhi.le
      (mem_map_of_mem Q.subtype (pth_power_mem_frattini_of_isPGroup (p := 2) q))
    apply Subtype.ext
    change (q : G) ^ 4 = 1
    simpa only [← pow_mul] using
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) _ hsq
  refine ⟨hc, ?_⟩
  have hn : ¬ Monoid.exponent Q ∣ 2 := by
    intro hd
    have hab : IsMulCommutative Q := ⟨⟨fun a b =>
      (Commute.of_orderOf_dvd_two (fun q => (Monoid.order_dvd_exponent q).trans hd) a b).eq⟩⟩
    have hle := Group.IsNilpotent.nilpotencyClass_le_one_iff.mpr hab
    omega
  obtain ⟨n, hnle, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Monoid.exponent Q ∣ 2 ^ 2 from hexp)
  interval_cases n
  · exact (hn (by rw [heq]; decide)).elim
  · exact (hn (by rw [heq]; decide)).elim
  · exact heq

end CFSG.Quasithin.Chapter14.Section06
