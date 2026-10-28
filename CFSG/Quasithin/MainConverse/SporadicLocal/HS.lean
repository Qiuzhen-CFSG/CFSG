module

public import CFSG.Quasithin.MainConverse.SporadicLocal.Criteria
public import CFSG.Quasithin.MainConverse.SporadicLocal.HS.EvenLocalCover
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound

/-!
# The Higman–Sims converse: quasithinness and even characteristic

Source: Aschbacher–Smith, Theorem 0.1.2(5), printed pp.4 and 482, and
GLS volume 3, Table 5.3m (printed p.274).

The degree-100 ATLAS carrier contains a kernel-certified nonabelian group
of order 125. The certified ambient order bound
`2^9 * 3^2 * 5^3 * 7 * 11` makes this subgroup Sylow and excludes every
other odd prime cube.
Consequently the whole group, and hence all its two-locals, has odd rank
at most two.

For condition E, the exhaustive normal elementary catalogue in the explicit
order-512 Sylow subgroup identifies every maximal two-local containing it
with one of three actual normalizers. Each has a constructed intrinsic
normal self-centralizing two-subgroup. `EvenLocalCover` assembles these
calculations, and the order bound discharges its last premise here.

The final theorem transports QT and E across an actual multiplicative
equivalence with this carrier, which is `ClassificationModels.SporadicName.hs.Carrier`.
All model obligations are discharged; simplicity is unnecessary for these
two conditions, and proper K remains the separate source induction input.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal
open Subgroup
open Sporadic.LeechRelated.HS

private theorem hs_odd_cube_not_dvd {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hne : p ≠ 5) : ¬ p ^ 3 ∣ 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11 := by
  intro hd
  have hpd : p ∣ 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11 :=
    (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  simp only [hp.dvd_mul] at hpd
  have hcases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
    rcases hpd with (((h2 | h3) | h5) | h7) | h11
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
        (hp.dvd_of_dvd_pow h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
        (hp.dvd_of_dvd_pow h3)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
        (hp.dvd_of_dvd_pow h5))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h7))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h11))))
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · exact ho.not_two_dvd_nat (dvd_refl 2)
  · norm_num at hd
  · exact hne rfl
  · norm_num at hd
  · norm_num at hd

/-- The certified subgroup of order 125 is Sylow under the ambient order bound. -/
public theorem hs_exists_nonabelian_sylow_five_of_card_dvd
    (hcard : Nat.card Carrier ∣ 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11) :
    ∃ P : Sylow 5 Carrier, Nat.card P = 5 ^ 3 ∧ ¬ IsMulCommutative P := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hindex : ¬ 5 ∣ FiveSubgroup.subgroup.index := by
    intro h
    have hd : 5 ^ 4 ∣ Nat.card Carrier := by
      rw [← FiveSubgroup.subgroup.card_mul_index, FiveSubgroup.card_subgroup]
      exact Nat.mul_dvd_mul_left (5 ^ 3) h
    have he := hd.trans hcard
    norm_num at he
  exact ⟨FiveSubgroup.subgroup_isPGroup.toSylow hindex,
    FiveSubgroup.card_subgroup, FiveSubgroup.subgroup_not_commutative⟩

/-- A divisibility bound on the actual permutation carrier suffices for all odd ranks. -/
public theorem hs_stronglyQuasithin_of_card_dvd
    (hcard : Nat.card Carrier ∣ 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11) :
    IsStronglyQuasithin Carrier := by
  apply stronglyQuasithin_of_odd_sylow_cases
  intro p hp ho
  by_cases h5 : p = 5
  · subst p
    exact Or.inr (hs_exists_nonabelian_sylow_five_of_card_dvd hcard)
  · exact Or.inl (fun hd => hs_odd_cube_not_dvd hp ho h5 (hd.trans hcard))

/-- Transport QT across an actual equivalence with the degree-100 carrier. -/
public theorem hs_quasithin_of_equiv_of_card_dvd
    {G : Type*} [Group G] [Finite G] (e : G ≃* Carrier)
    (hcard : Nat.card Carrier ∣ 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11) :
    IsQuasithin G := by
  have hG : IsStronglyQuasithin G := by
    intro p hp ho
    exact (Theory.GroupTheory.primeRank_le_of_injective p e.toMonoidHom e.injective).trans
      (hs_stronglyQuasithin_of_card_dvd hcard p hp ho)
  exact hG.quasithin

/-- Conditional final assembly. Both the ambient order bound and the exhaustive
Sylow-containing local cover must be discharged in the ATLAS carrier. -/
public theorem hs_qt_e_of_order_bound_and_local_cover
    {G : Type*} [Group G] [Finite G] (e : G ≃* Carrier)
    (hcard : Nat.card Carrier ∣ 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11)
    {ι : Type*} (T : Sylow 2 Carrier) (L : ι → Subgroup Carrier)
    (Q : ∀ i, Subgroup (L i))
    (hn : ∀ i, (Q i).Normal) (hp : ∀ i, IsPGroup 2 (Q i))
    (hc : ∀ i, centralizer (Q i : Set (L i)) ≤ Q i)
    (hcover : ∀ M : Subgroup Carrier, IsMaximalTwoLocal M → (T : Subgroup Carrier) ≤ M →
      ∃ i, Nonempty (M ≃* L i)) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  exact ⟨hs_quasithin_of_equiv_of_card_dvd e hcard,
    evenCharacteristic_of_model_equiv e
      (evenCharacteristic_of_local_normal_cover T L Q hn hp hc hcover)⟩

/-- The exact degree-100 ATLAS carrier has odd prime rank at most two. -/
public theorem hs_stronglyQuasithin : IsStronglyQuasithin Carrier :=
  hs_stronglyQuasithin_of_card_dvd card_carrier_dvd

/-- Every maximal two-local containing a fixed Sylow two-subgroup has
self-centralizing intrinsic two-core. All concrete model inputs are discharged. -/
public theorem hs_evenCharacteristic : IsEvenCharacteristic Carrier :=
  HSEvenLocalCover.evenCharacteristic_of_card_dvd card_carrier_dvd

/-- Quasithinness for any group actually isomorphic to the ATLAS HS carrier. -/
public theorem hs_quasithin_of_equiv
    {G : Type*} [Group G] [Finite G] (e : G ≃* Carrier) :
    IsQuasithin G :=
  hs_quasithin_of_equiv_of_card_dvd e card_carrier_dvd

/-- The HS case of conditions QT and E in Theorem 0.1.2(5). The input is an
actual equivalence with the fixed carrier, with no remaining order or local premises. -/
public theorem hs_qt_e_of_equiv
    {G : Type*} [Group G] [Finite G] (e : G ≃* Carrier) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  ⟨hs_quasithin_of_equiv e, evenCharacteristic_of_model_equiv e hs_evenCharacteristic⟩

end CFSG.Quasithin.MainConverse.SporadicLocal
