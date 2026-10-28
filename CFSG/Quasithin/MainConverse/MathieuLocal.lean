module

public import CFSG.Quasithin.MainConverse.SmallModels
public import CFSG.Quasithin.MainConverse.Transport
public import CFSG.Quasithin.MainConverse.MathieuLocal.M11Even
public import CFSG.Quasithin.MainConverse.MathieuLocal.M12Even
public import CFSG.Quasithin.MainConverse.MathieuLocal.M22Even
public import CFSG.Quasithin.MainConverse.MathieuLocal.M23Even
public import CFSG.Quasithin.MainConverse.MathieuLocal.M24Even
public import Theory.Mathieu.ThreeRank

/-!
# Mathieu calculations for the classification converse

The concrete M12 and M24 carriers have nonabelian Sylow 3-subgroups of
order 27. Their 3-ranks are therefore at most two. Every other odd prime
occurs with exponent at most two in their checked orders. Thus both groups
are strongly quasithin, which bounds the odd-prime ranks of every 2-local.
Together with `SmallModels`, this supplies QT for all five Mathieu groups.

The imported local calculations prove E for all five actual carriers. M11
and M12 use exhaustive normal elementary subgroup calculations in a fixed
Sylow subgroup. M22, M23 and M24 use involution centralizers and the
Sylow-center criterion to cover every required local overgroup. All cores
and normality assertions are intrinsic to their local groups.

Actual group isomorphisms transport both QT and E to the classification
models. The QTKE wrappers retain proper K as the explicit induction input;
their QT and E conclusions have no additional hypotheses.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(5), printed p.4, repeated as Theorem 0.1.1(5) on p.482.
-/

namespace CFSG.Quasithin.MainConverse
open Sporadic.Mathieu

public theorem m12_stronglyQuasithin : IsStronglyQuasithin M12 := by
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  by_cases h3 : p = 3
  · simpa [h3] using m12_primeRank_three_le_two
  apply primeRank_le_two_of_cube_not_dvd
  intro hd
  have hpd : p ∣ Nat.card M12 := (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  rcases (m12_prime_dvd_order_iff p).mp hpd with rfl | rfl | rfl | rfl
  · exact ho.not_two_dvd_nat (dvd_refl 2)
  · exact h3 rfl
  all_goals rw [m12_order] at hd; norm_num at hd

public theorem m24_stronglyQuasithin : IsStronglyQuasithin M24 := by
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  by_cases h3 : p = 3
  · simpa [h3] using m24_primeRank_three_le_two
  apply primeRank_le_two_of_cube_not_dvd
  intro hd
  have hpd : p ∣ Nat.card M24 := (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  rcases (m24_prime_dvd_order_iff p).mp hpd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ho.not_two_dvd_nat (dvd_refl 2)
  · exact h3 rfl
  all_goals rw [m24_order] at hd; norm_num at hd

public theorem m12_quasithin : IsQuasithin M12 := m12_stronglyQuasithin.quasithin

public theorem m24_quasithin : IsQuasithin M24 := m24_stronglyQuasithin.quasithin

public theorem m12_quasithin_of_iso {G : Type*} [Group G] [Finite G]
    (e : G ≃* M12) : IsQuasithin G :=
  quasithin_of_model_equiv e m12_quasithin

public theorem m24_quasithin_of_iso {G : Type*} [Group G] [Finite G]
    (e : G ≃* M24) : IsQuasithin G :=
  quasithin_of_model_equiv e m24_quasithin

section

variable {G : Type*} [Group G] [Finite G]

/-- Condition E for any group actually isomorphic to M11. -/
public theorem m11_evenCharacteristic_of_iso (e : G ≃* M11) :
    IsEvenCharacteristic G :=
  evenCharacteristic_of_model_equiv e m11_evenCharacteristic

/-- Condition E for any group actually isomorphic to M12. -/
public theorem m12_evenCharacteristic_of_iso (e : G ≃* M12) :
    IsEvenCharacteristic G :=
  evenCharacteristic_of_model_equiv e m12_evenCharacteristic

/-- Condition E for any group actually isomorphic to M22. -/
public theorem m22_evenCharacteristic_of_iso (e : G ≃* M22) :
    IsEvenCharacteristic G :=
  evenCharacteristic_of_model_equiv e m22_evenCharacteristic

/-- Condition E for any group actually isomorphic to M23. -/
public theorem m23_evenCharacteristic_of_iso (e : G ≃* M23) :
    IsEvenCharacteristic G :=
  evenCharacteristic_of_model_equiv e m23_evenCharacteristic

/-- Condition E for any group actually isomorphic to M24. -/
public theorem m24_evenCharacteristic_of_iso (e : G ≃* M24) :
    IsEvenCharacteristic G :=
  evenCharacteristic_of_model_equiv e m24_evenCharacteristic

/-- The QT and E clauses of the M11 branch of the source converse. -/
public theorem m11_quasithin_and_evenCharacteristic_of_iso (e : G ≃* M11) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  ⟨m11_quasithin_of_iso e, m11_evenCharacteristic_of_iso e⟩

/-- The QT and E clauses of the M12 branch of the source converse. -/
public theorem m12_quasithin_and_evenCharacteristic_of_iso (e : G ≃* M12) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  ⟨m12_quasithin_of_iso e, m12_evenCharacteristic_of_iso e⟩

/-- The QT and E clauses of the M22 branch of the source converse. -/
public theorem m22_quasithin_and_evenCharacteristic_of_iso (e : G ≃* M22) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  ⟨m22_quasithin_of_iso e, m22_evenCharacteristic_of_iso e⟩

/-- The QT and E clauses of the M23 branch of the source converse. -/
public theorem m23_quasithin_and_evenCharacteristic_of_iso (e : G ≃* M23) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  ⟨m23_quasithin_of_iso e, m23_evenCharacteristic_of_iso e⟩

/-- The QT and E clauses of the M24 branch of the source converse. -/
public theorem m24_quasithin_and_evenCharacteristic_of_iso (e : G ≃* M24) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  ⟨m24_quasithin_of_iso e, m24_evenCharacteristic_of_iso e⟩

/-- The M11 converse under the proper-K induction hypothesis. -/
public theorem m11_isQTKE_of_iso_of_properK {K : GroupClass}
    (e : G ≃* M11) (hK : HasProperKSubgroups K G) : IsQTKE K G := by
  obtain ⟨hQT, hE⟩ := m11_quasithin_and_evenCharacteristic_of_iso e
  exact ⟨hQT, hK, hE⟩

/-- The M12 converse under the proper-K induction hypothesis. -/
public theorem m12_isQTKE_of_iso_of_properK {K : GroupClass}
    (e : G ≃* M12) (hK : HasProperKSubgroups K G) : IsQTKE K G := by
  obtain ⟨hQT, hE⟩ := m12_quasithin_and_evenCharacteristic_of_iso e
  exact ⟨hQT, hK, hE⟩

/-- The M22 converse under the proper-K induction hypothesis. -/
public theorem m22_isQTKE_of_iso_of_properK {K : GroupClass}
    (e : G ≃* M22) (hK : HasProperKSubgroups K G) : IsQTKE K G := by
  obtain ⟨hQT, hE⟩ := m22_quasithin_and_evenCharacteristic_of_iso e
  exact ⟨hQT, hK, hE⟩

/-- The M23 converse under the proper-K induction hypothesis. -/
public theorem m23_isQTKE_of_iso_of_properK {K : GroupClass}
    (e : G ≃* M23) (hK : HasProperKSubgroups K G) : IsQTKE K G := by
  obtain ⟨hQT, hE⟩ := m23_quasithin_and_evenCharacteristic_of_iso e
  exact ⟨hQT, hK, hE⟩

/-- The M24 converse under the proper-K induction hypothesis. -/
public theorem m24_isQTKE_of_iso_of_properK {K : GroupClass}
    (e : G ≃* M24) (hK : HasProperKSubgroups K G) : IsQTKE K G := by
  obtain ⟨hQT, hE⟩ := m24_quasithin_and_evenCharacteristic_of_iso e
  exact ⟨hQT, hK, hE⟩

end

end CFSG.Quasithin.MainConverse
