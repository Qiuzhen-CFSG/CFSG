module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.OuterGeneration
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.OuterOriginalConsumer
/-!
# The actual PSL₃(3) source two-core is the central involution

The inner-action branch is already impossible. In the outer branch the
core is cyclic of order dividing four, while the order-four case contradicts
the source central four. The original central-core involution therefore
generates the whole core. The final consumer chooses every mark from the
original tuple and proves |O₂(H)|=2 without extra geometric premises.
Source: Aschbacher--Smith 2.5.15, printed p.559.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M U L : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem linear_three_source_core_eq_central_involution
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (hp : (U,L) ∈ largestLocalPairs M H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (e : K ≃* Matrix.PSL3Three.PSL)
    (t : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hZ : IsKleinFour (centerIn ((S : Subgroup H).map H.subtype)))
    (k : K) (hk : orderOf k = 2)
    (hkZ : (k : G) ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hspan : centerIn ((S : Subgroup H).map H.subtype) = zpowers t ⊔ zpowers (k : G)) :
    twoCore H = zpowers t := by
  have hres := (MathieuSourceSetup.small_component_centralizer_residual c hG hempty hgen
    (Or.inl ⟨e⟩) t ht htC htZ).2.2
  have hout : ¬ (S : Subgroup H).map H.subtype ≤ K ⊔ centralizer (K : Set G) := by
    intro hin
    exact small_component_inner_residual_false c hG hempty hgen hb hp hUS (Or.inl ⟨e⟩)
      hin t ht htC htZ hZ k hk hkZ hspan hres
  let Y := (S : Subgroup H).map H.subtype
  have hN := local_residual_normalized_by_sylow_normalizer K Y (Or.inl ⟨e⟩) k hk t hspan hres
  obtain ⟨x,hxT,hxS,hxN,_⟩ := exists_outside_normalizer_square_mem Y c.T c.T.isPGroup' c.sylow_lt
  obtain ⟨x,hxT,hxS,hxN,hxR⟩ := local_residual_crossing_adjustment c (Or.inl ⟨e⟩)
    k hk hkZ hxT hxS hxN (hN hxN)
  have hi := MathieuSourceSetup.source_normalizer_index_two c hG hempty hgen hb
  let N := (c.T : Subgroup G) ⊓ normalizer (Y : Set G)
  have hx2 : x^2 ∈ Y := (Y.subgroupOf N).sq_mem_of_index_two hi ⟨x,hxT,hxN⟩
  have hn4 := linear_three_source_core_not_four c hG hempty hgen e k hk hout
    (Y.le_normalizer.trans hN) hZ hxT hxS hxN hx2 hxR
  have hd := (linear_three_source_core_cyclic_dvd_four c hG hempty hgen e k hk hxT hxS hxN hx2 hxR).2
  have hd2 : 2 ∣ Nat.card (twoCore H) := ht ▸ (twoCore H).orderOf_dvd_natCard htC
  have hcard : Nat.card (twoCore H) = 2 := by
    have hle := Nat.le_of_dvd Nat.card_pos hd2
    have hd' : Nat.card (twoCore H) ∣ 2^2 := hd
    obtain ⟨n,hn,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd'
    interval_cases n
    · have hc1 : Nat.card (twoCore H) = 1 := by simpa only [pow_zero] using he
      rw [hc1] at hd2
      norm_num at hd2
    · simpa only [pow_one] using he
    · exact False.elim (hn4 (by simpa only [show (2:ℕ)^2=4 from rfl] using he))
  exact (eq_of_le_of_card_ge (zpowers_le.mpr htC) (by rw [hcard,Nat.card_zpowers,ht])).symm

theorem linear_three_source_twoCore_card
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (hp : (U,L) ∈ largestLocalPairs M H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (e : K ≃* Matrix.PSL3Three.PSL) : Nat.card (twoCore H) = 2 := by
  let Y := (S : Subgroup H).map H.subtype
  obtain ⟨t,k,ht,hk,htC,hcore,hline,_,hspanK,hZ,_⟩ :=
    ComponentSelection.MathieuSourceSetup.source_central_marks c hG hempty hgen hb
  have htZ : t ∈ centerIn Y := by
    have hh : t ∈ centerIn Y ⊓ twoCore H := hcore ▸ mem_zpowers t
    exact hh.1
  have hKY : Y ≤ normalizer (K : Set G) := (map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance)
  have horbit : componentOrbit K Y = K := le_antisymm
    (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hKY) (le_componentOrbit _ _)
  have hkZK : k ∈ centerIn Y ⊓ K := by
    rw [horbit] at hline
    exact hline ▸ mem_zpowers k
  let zK : K := ⟨k,hkZK.2⟩
  have hzK : orderOf zK = 2 := by simpa only [zK,Subgroup.orderOf_mk] using hk
  rw [linear_three_source_core_eq_central_involution c hG hempty hgen hb hp hUS e
    t ht htC htZ hZ zK hzK hkZK.1 hspanK,Nat.card_zpowers,ht]

end CFSG.Quasithin.Chapter2.Section05
