module

public import CFSG.Quasithin.MainConverse.SmallModels
public import CFSG.Quasithin.MainConverse.Transport
public import CFSG.Quasithin.MainConverse.AlternatingLocal.EightNineEven
public import CFSG.Quasithin.MainConverse.AlternatingLocal.NineNormalizerOrder
public import Theory.GroupTheory.TwoLocalInvolutionCentralizers
public import Theory.SpecificGroups.Alternating.SmallInvolutionCentralizers

/-!
# Alternating-group local calculations for the converse

In A₅ and A₆ every involution centralizer is a two-group. Consequently each
two-local has a self-centralizing two-core, which proves the source condition E.
Transport gives the same result for actual isomorphic copies.

For A₉ the order bound handles all odd primes except three. The orbit-counting
calculation in NineNormalizerOrder excludes 27 from the orders of normalizers
of nonidentity two-subgroups, completing QT. The imported EightNineEven module
proves E for A₈ via its constructed equivalence with PSL₄(2), and for A₉ by
descent to an eight-point stabilizer. SmallModels supplies QT for A₅, A₆, and A₈.

Thus QT and E hold unconditionally for all four alternating models and their
actual isomorphic copies. The final QTKE wrapper retains proper K as the
explicit induction hypothesis; it does not require a separate classification
of the models' proper sections.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(3), printed p.4, repeated on p.482; condition E on printed p.3.
-/

namespace CFSG.Quasithin.MainConverse

open Subgroup

/-- In particular, the concrete groups A₅ and A₆ satisfy condition E. -/
public theorem alternating_evenCharacteristic_of_degree_le_six
    {n : ℕ} (hn : n ≤ 6) : IsEvenCharacteristic (alternatingGroup (Fin n)) := by
  intro T M hM _
  exact Theory.GroupTheory.twoLocal_centralizer_pCore_le_of_involution_centralizers
    (alternatingGroup.isPGroup_centralizer_involution_of_degree_le_six hn) M hM.1

/-- Transport the small-degree calculation through an actual model equivalence. -/
public theorem alternating_evenCharacteristic_of_degree_le_six_of_iso
    {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : n ≤ 6)
    (e : G ≃* alternatingGroup (Fin n)) : IsEvenCharacteristic G :=
  evenCharacteristic_of_model_equiv e (alternating_evenCharacteristic_of_degree_le_six hn)

private theorem alternatingNine_odd_cube_not_dvd {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3) :
    ¬ p ^ 3 ∣ Nat.card (alternatingGroup (Fin 9)) := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]
  intro hd
  have hpd : p ∣ 181440 := (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  rw [show 181440 = 2 * 2 * 2 * 2 * 2 * 2 * 3 * 3 * 3 * 3 * 5 * 7 by decide] at hpd
  have hcases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    simpa only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
      or_self, or_assoc, or_self_left] using hpd
  rcases hcases with rfl | rfl | rfl | rfl
  · exact ho.not_two_dvd_nat (dvd_refl 2)
  · exact hp3 rfl
  · norm_num at hd
  · norm_num at hd

/-- The normalizer-order calculation suffices for QT in A₉.
The unconditional theorem below supplies this premise for the actual two-subgroups. -/
public theorem alternatingNine_quasithin_of_normalizer_card
    (hN : ∀ Q : Subgroup (alternatingGroup (Fin 9)), Q ≠ ⊥ → IsPGroup 2 Q →
      ¬ 27 ∣ Nat.card (normalizer (Q : Set (alternatingGroup (Fin 9))))) :
    IsQuasithin (alternatingGroup (Fin 9)) := by
  apply isQuasithin_iff_twoLocal.mpr
  rintro M ⟨Q, hQ, hpQ, rfl⟩
  apply stronglyQuasithin_of_odd_cube_not_dvd
  intro p hp ho
  by_cases hp3 : p = 3
  · subst p
    exact hN Q hQ hpQ
  · intro hd
    exact alternatingNine_odd_cube_not_dvd hp ho hp3
      (hd.trans (normalizer (Q : Set (alternatingGroup (Fin 9)))).card_subgroup_dvd_card)

/-- The same normalizer calculation gives QT for isomorphic copies of A₉. -/
public theorem alternatingNine_quasithin_of_normalizer_card_of_iso
    {G : Type*} [Group G] [Finite G]
    (hN : ∀ Q : Subgroup (alternatingGroup (Fin 9)), Q ≠ ⊥ → IsPGroup 2 Q →
      ¬ 27 ∣ Nat.card (normalizer (Q : Set (alternatingGroup (Fin 9)))))
    (e : G ≃* alternatingGroup (Fin 9)) : IsQuasithin G :=
  quasithin_of_model_equiv e (alternatingNine_quasithin_of_normalizer_card hN)

/-- The actual alternating group on nine points is quasithin. -/
public theorem alternatingNine_quasithin : IsQuasithin (alternatingGroup (Fin 9)) :=
  alternatingNine_quasithin_of_normalizer_card alternatingNine_normalizer_card_not_dvd_27

/-- Quasithinness for every group actually isomorphic to A₉. -/
public theorem alternatingNine_quasithin_of_iso
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* alternatingGroup (Fin 9)) : IsQuasithin G :=
  quasithin_of_model_equiv e alternatingNine_quasithin

/-- All four alternating groups in the source list are quasithin. -/
public theorem alternating_quasithin {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8 ∨ n = 9) :
    IsQuasithin (alternatingGroup (Fin n)) := by
  rcases hn with h5 | h6 | h8 | rfl
  · exact (alternating_stronglyQuasithin (Or.inl h5)).quasithin
  · exact (alternating_stronglyQuasithin (Or.inr (Or.inl h6))).quasithin
  · exact (alternating_stronglyQuasithin (Or.inr (Or.inr h8))).quasithin
  · exact alternatingNine_quasithin

/-- All four alternating groups in the source list satisfy condition E. -/
public theorem alternating_evenCharacteristic {n : ℕ}
    (hn : n = 5 ∨ n = 6 ∨ n = 8 ∨ n = 9) :
    IsEvenCharacteristic (alternatingGroup (Fin n)) := by
  rcases hn with rfl | rfl | rfl | rfl
  · exact alternating_evenCharacteristic_of_degree_le_six (by decide)
  · exact alternating_evenCharacteristic_of_degree_le_six (by decide)
  · exact alternatingEight_evenCharacteristic
  · exact alternatingNine_evenCharacteristic

/-- Condition E for actual isomorphic copies of all four alternating models. -/
public theorem alternating_evenCharacteristic_of_iso
    {G : Type*} [Group G] [Finite G] {n : ℕ}
    (hn : n = 5 ∨ n = 6 ∨ n = 8 ∨ n = 9)
    (e : G ≃* alternatingGroup (Fin n)) : IsEvenCharacteristic G :=
  evenCharacteristic_of_model_equiv e (alternating_evenCharacteristic hn)

/-- The QT and E clauses of the alternating branch of the source converse. -/
public theorem alternating_quasithin_and_evenCharacteristic {n : ℕ}
    (hn : n = 5 ∨ n = 6 ∨ n = 8 ∨ n = 9) :
    IsQuasithin (alternatingGroup (Fin n)) ∧
      IsEvenCharacteristic (alternatingGroup (Fin n)) :=
  ⟨alternating_quasithin hn, alternating_evenCharacteristic hn⟩

/-- The alternating branch with its actual model equivalence, in any universe. -/
public theorem alternating_quasithin_and_evenCharacteristic_of_iso
    {G : Type*} [Group G] [Finite G] {n : ℕ}
    (hn : n = 5 ∨ n = 6 ∨ n = 8 ∨ n = 9)
    (e : G ≃* alternatingGroup (Fin n)) : IsQuasithin G ∧ IsEvenCharacteristic G :=
  ⟨quasithin_of_model_equiv e (alternating_quasithin hn),
    alternating_evenCharacteristic_of_iso hn e⟩

/-- The alternating converse under the proper-K induction hypothesis.
Both QT and E are supplied by the concrete calculations, independently of K. -/
public theorem alternating_isQTKE_of_iso_of_properK
    {G : Type*} [Group G] [Finite G] {K : GroupClass} {n : ℕ}
    (hn : n = 5 ∨ n = 6 ∨ n = 8 ∨ n = 9)
    (e : G ≃* alternatingGroup (Fin n)) (hK : HasProperKSubgroups K G) :
    IsQTKE K G := by
  obtain ⟨hQT, hE⟩ := alternating_quasithin_and_evenCharacteristic_of_iso hn e
  exact ⟨hQT, hK, hE⟩

end CFSG.Quasithin.MainConverse
