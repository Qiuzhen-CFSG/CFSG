module

public import Theory.GroupTheory.RankTwoNormalAbelian
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.CoprimeQuotientNormalizer
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Central involutions in rank-two odd quotients

A nontrivial normal two-subgroup of elementary rank at most two has cyclic
center if the ambient group has no normal elementary four-group. The first
omega subgroup of that center is normal of order two, hence central in the
ambient group.

A central involution in an odd quotient lifts to an involution in any chosen
Sylow two-subgroup. The lift centralizes that Sylow subgroup, and its
centralizer supplements the odd kernel. This follows from injectivity on the
Sylow subgroup and normalizer lifting through a coprime kernel.

These elementary reductions support the rank-two cases of GLS2, Chapter F,
Sections 21–22. They do not assert any ambient commuting-component control.
-/

namespace Subgroup

/-- A nontrivial normal two-subgroup of rank at most two supplies an ambient
central involution when no normal elementary four exists. -/
public theorem exists_central_involution_of_rank_two_normal_twoGroup
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hrank : ∀ D : Subgroup G, IsElementaryAbelian 2 D → D ≤ Q → Nat.card D < 8)
    (hno : ∀ U : Subgroup G, U.Normal → IsElementaryAbelian 2 U → Nat.card U ≠ 4) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ center G ∧ z ∈ Q := by
  let : Nontrivial Q := Q.nontrivial_iff_ne_bot.mpr hne
  let : Nontrivial (center Q) := hQ.center_nontrivial
  let B := (center Q).map Q.subtype
  let : B.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsMulCommutative B := Subgroup.map_isMulCommutative (center Q) Q.subtype
  have hBQ : B ≤ Q := map_subtype_le _
  have hB : IsPGroup 2 B := hQ.to_le hBQ
  have hBne : B ≠ ⊥ := by
    intro h
    have hc : Nat.card B = 1 := Subgroup.card_eq_one.mpr h
    change Nat.card ((center Q).map Q.subtype) = 1 at hc
    rw [card_map_of_injective Q.subtype_injective] at hc
    have := Finite.one_lt_card (α := center Q)
    omega
  let : IsCyclic B := isCyclic_of_normal_abelian_of_no_normal_four B hB
    (fun D hD hDB => hrank D hD (hDB.trans hBQ)) hno
  let O := omega₁ B (p := 2)
  let : O.Characteristic := omega₁_characteristic B
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative B
  have hdiv : 2 ∣ Nat.card B := hB.card_eq_or_dvd.resolve_left
    (fun h => hBne (Subgroup.card_eq_one.mp h))
  let U := O.map B.subtype
  let : U.Normal := ConjAct.normal_of_characteristic_of_normal
  have hUne : U ≠ ⊥ := omega₁_map_subtype_ne_bot B 2 hdiv
  have hUcard : Nat.card U = 2 := by
    have hd : Nat.card O ∣ 2 := by
      rw [← IsCyclic.exponent_eq_card]
      exact IsElementaryAbelian.exponent_dvd_p 2 O
    have hc : Nat.card O = 1 ∨ Nat.card O = 2 := (Nat.dvd_prime Nat.prime_two).mp hd
    change Nat.card (O.map B.subtype) = 2
    rw [card_map_of_injective B.subtype_injective]
    rcases hc with h | h
    · exact False.elim (hUne (Subgroup.card_eq_one.mp (by
        change Nat.card (O.map B.subtype) = 1
        rw [card_map_of_injective B.subtype_injective, h])))
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hUcard])
  exact ⟨z, (Subgroup.orderOf_coe z).trans hz,
    central_of_normal_card_two U hUcard z.property,
    hBQ (map_subtype_le O z.property)⟩

/-- A central involution of an odd quotient lifts to a Sylow-central
involution whose centralizer supplements the odd kernel. -/
public theorem exists_sylow_central_involution_supplement_of_odd_quotient
    {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hodd : Nat.Coprime 2 (Nat.card N))
    (P : Sylow 2 G) (z : G ⧸ N) (hz : orderOf z = 2) (hzc : z ∈ center (G ⧸ N)) :
    ∃ t : G, orderOf t = 2 ∧ t ∈ P ∧
      (P : Subgroup G) ≤ centralizer ({t} : Set G) ∧
      QuotientGroup.mk' N t = z ∧ centralizer ({t} : Set G) ⊔ N = ⊤ := by
  let q := QuotientGroup.mk' N
  let Pbar := P.mapSurjective (QuotientGroup.mk'_surjective N)
  let Z := zpowers z
  have hZcenter : Z ≤ center (G ⧸ N) := zpowers_le.mpr hzc
  let : Z.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hc := mem_center_iff.mp (hZcenter hn) g
    simpa [hc, mul_assoc] using hn
  have hZtwo : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by
    change Nat.card (zpowers z) = 2 ^ 1
    rw [Nat.card_zpowers, hz, pow_one])
  have hzP : z ∈ Pbar := hZtwo.le_sylow_of_normal Pbar (mem_zpowers z)
  change z ∈ (P : Subgroup G).map q at hzP
  obtain ⟨t, htP, htz⟩ := hzP
  let f := q.comp (P : Subgroup G).subtype
  have hf : Function.Injective f := injective_comp_subtype_of_coprime_ker q
    (by simpa only [q, QuotientGroup.ker_mk'] using hodd) P P.isPGroup'
  have ht : orderOf t = 2 := by
    have ho := (orderOf_injective f hf (⟨t, htP⟩ : P)).symm
    exact (Subgroup.orderOf_coe (⟨t, htP⟩ : P)).trans
      (ho.trans ((congrArg orderOf htz).trans hz))
  have hPC : (P : Subgroup G) ≤ centralizer ({t} : Set G) := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    have heq : (⟨x, hx⟩ : P) * ⟨t, htP⟩ = ⟨t, htP⟩ * ⟨x, hx⟩ := by
      apply hf
      change q (x * t) = q (t * x)
      rw [map_mul, map_mul, htz]
      exact mem_center_iff.mp hzc _
    exact congrArg Subtype.val heq
  refine ⟨t, ht, htP, hPC, htz, ?_⟩
  let T := zpowers t
  let : Fact (IsPGroup 2 T) := ⟨IsPGroup.of_card (n := 1) (by
    change Nat.card (zpowers t) = 2 ^ 1
    rw [Nat.card_zpowers, ht, pow_one])⟩
  have hmap : T.map q = Z := by
    change (zpowers t).map q = zpowers z
    rw [MonoidHom.map_zpowers, htz]
  have hnorm : (normalizer (T : Set G)).map q = ⊤ := by
    rw [← normalizer_map_quotient_eq_map_normalizer 2 T N inferInstance hodd,
      hmap, normalizer_eq_top]
  have hh := congrArg (Subgroup.comap q) hnorm
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', comap_top,
    normalizer_zpowers_eq_centralizer_of_order_two t ht] at hh
  exact hh

end Subgroup
