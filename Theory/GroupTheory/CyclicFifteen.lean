module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic.NormNum

/-!
# Groups of order fifteen

Both Sylow subgroups of a group of order fifteen are normal: their numbers
respectively divide five and three and are one modulo three and five.
Generators of the two subgroups commute, and their product has order fifteen.
This elementary fact supplies cyclic complements in Lyons's Lemma 1(c),
*A Characterization of the Group U₃(4)* (1972), pp. 372–373.
-/

public theorem isCyclic_of_card_eq_fifteen {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 15) : IsCyclic G := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := 3) (G := G)
  obtain ⟨Q⟩ := Sylow.nonempty (p := 5) (G := G)
  have hP : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity, hG, show 15 = 3 * 5 from rfl,
      Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.Prime.factorization (by decide : Nat.Prime 3),
      Nat.Prime.factorization (by decide : Nat.Prime 5)]
  have hQ : Nat.card Q = 5 := by
    rw [Q.card_eq_multiplicity, hG, show 15 = 3 * 5 from rfl,
      Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.Prime.factorization (by decide : Nat.Prime 3),
      Nat.Prime.factorization (by decide : Nat.Prime 5)]
  have hPi : P.index = 5 := by
    have hi := (P : Subgroup G).card_mul_index
    rw [hP, hG] at hi
    omega
  have hQi : Q.index = 3 := by
    have hi := (Q : Subgroup G).card_mul_index
    rw [hQ, hG] at hi
    omega
  have hPn : Nat.card (Sylow 3 G) = 1 := by
    have hd := P.card_dvd_index
    rw [hPi] at hd
    have hm := card_sylow_modEq_one 3 G
    have he := (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd
    rcases he with he | he
    · exact he
    · rw [he] at hm
      norm_num [Nat.ModEq] at hm
  have hQn : Nat.card (Sylow 5 G) = 1 := by
    have hd := Q.card_dvd_index
    rw [hQi] at hd
    have hm := card_sylow_modEq_one 5 G
    have he := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd
    rcases he with he | he
    · exact he
    · rw [he] at hm
      norm_num [Nat.ModEq] at hm
  let : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp hPn).1
  let : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp hQn).1
  have hPN : (P : Subgroup G).Normal := P.normal_of_subsingleton
  have hQN : (Q : Subgroup G).Normal := Q.normal_of_subsingleton
  let : IsCyclic P := isCyclic_of_prime_card hP
  let : IsCyclic Q := isCyclic_of_prime_card hQ
  obtain ⟨x, hx⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic P)
  obtain ⟨y, hy⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic Q)
  have hxG : orderOf (x : G) = 3 := (Subgroup.orderOf_coe x).trans (hx.trans hP)
  have hyG : orderOf (y : G) = 5 := (Subgroup.orderOf_coe y).trans (hy.trans hQ)
  have hd : Disjoint (P : Subgroup G) (Q : Subgroup G) :=
    Subgroup.disjoint_of_coprime_natCard (by rw [hP, hQ]; decide)
  have hc : Commute (x : G) (y : G) :=
    Subgroup.commute_of_normal_of_disjoint _ _ hPN hQN hd x y x.property y.property
  apply isCyclic_of_orderOf_eq_card ((x : G) * (y : G))
  rw [hc.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hxG, hyG]; decide), hxG, hyG, hG]
