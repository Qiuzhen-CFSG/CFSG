module
public import Theory.GroupTheory.PGroup.CoprimeFrattiniAction
public import Theory.Frattini.PGroup

/-!
# Five-automorphisms of small three-groups

A finite three-group of order at most 81 with an automorphism of order five
is elementary abelian of order 81. Orbit counting modulo five first excludes
orders 1, 3, 9 and 27. The coprime Frattini-action theorem transfers the
order-five action faithfully to the Frattini quotient, whose order must also
be 81. The Frattini subgroup is therefore trivial.

This combines elementary orbit counting with the Burnside basis-kernel
theorem formalized in `PGroup.CoprimeFrattiniAction`.
-/

open Subgroup

private theorem card_eq_eightyone_of_five_dvd
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup 3 G)
    (hbound : Nat.card G ≤ 81) (hfive : 5 ∣ Nat.card (MulAut G)) :
    Nat.card G = 81 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨n, hn⟩ := hG.exists_card_eq
  have hnle : n ≤ 4 := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 3) hh
    rw [← hn] at hp
    norm_num at hp
    omega
  by_contra hne
  have hnlt : n ≤ 3 := by
    by_contra! hh
    have hn4 : n = 4 := by omega
    exact hne (by simpa [hn4] using hn)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 5 hfive
  let P := zpowers a
  have hP : Nat.card P = 5 := by rw [Nat.card_zpowers, ha]
  have hp : IsPGroup 5 P := IsPGroup.of_card (n := 1) (by simpa using hP)
  let F := FixedPoints.subgroup P G
  have hmod := hp.card_modEq_card_fixedPoints G
  change Nat.card G % 5 = Nat.card F % 5 at hmod
  have hFdiv : Nat.card F ∣ 3 ^ n := hn ▸ F.card_subgroup_dvd_card
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hFdiv
  have heq : Nat.card F = Nat.card G := by
    rw [hn, hcard] at hmod ⊢
    interval_cases n <;> interval_cases k <;> norm_num at *
  have htop := F.eq_top_of_card_eq heq
  have haone : a = 1 := by
    apply MulEquiv.ext
    intro x
    exact (show x ∈ F from htop ▸ mem_top x) ⟨a, mem_zpowers a⟩
  rw [haone, orderOf_one] at ha
  norm_num at ha

/-- A five-automorphism forces a three-group of order at most 81 to be elementary of order 81. -/
public theorem elementary_three_of_card_le_eightyone_of_five_dvd_card_mulAut
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup 3 G)
    (hbound : Nat.card G ≤ 81) (hfive : 5 ∣ Nat.card (MulAut G)) :
    Nat.card G = 81 ∧ IsElementaryAbelian 3 G := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (IsPGroup 3 G) := ⟨hG⟩
  have hcard := card_eq_eightyone_of_five_dvd hG hbound hfive
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 5 hfive
  let P := zpowers a
  have hP : Nat.card P = 5 := by rw [Nat.card_zpowers, ha]
  have hinj := MonoidHom.injective_frattini_action_of_coprime hG P.subtype
    P.subtype_injective (show Nat.Coprime (Nat.card P) 3 by rw [hP]; decide)
  have hdiv : 5 ∣ Nat.card (MulAut (G ⧸ frattini G)) := by
    rw [← hP]
    exact Subgroup.card_dvd_of_injective _ hinj
  have hquot : Nat.card (G ⧸ frattini G) = 81 :=
    card_eq_eightyone_of_five_dvd (hG.to_quotient (frattini G))
      ((Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card (frattini G))).trans hbound)
      hdiv
  have hprod := (frattini G).index_mul_card
  change Nat.card (G ⧸ frattini G) * Nat.card (frattini G) = Nat.card G at hprod
  rw [hcard, hquot] at hprod
  have hfrattini : frattini G = ⊥ := Subgroup.card_eq_one.mp (by omega)
  exact ⟨hcard, (frattini_eq_bot_iff_isElementaryAbelian (p := 3)).mp hfrattini⟩
