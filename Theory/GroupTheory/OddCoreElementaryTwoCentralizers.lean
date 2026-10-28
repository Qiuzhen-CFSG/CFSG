module
public import Theory.GroupTheory.OddThreeCentralizerContainment
public import Theory.ElementaryAbelian.Basic
public import Theory.PPrimeCore
/-!
# Trivial odd subgroups detected by a noncyclic elementary two-group

If a noncyclic elementary two-group normalizes an odd subgroup and each of
its nonidentity elements has a two-group centralizer, the odd subgroup is
trivial. Choose two different involutions in the elementary group. Its three
cyclic fixed subgroups lie in groups of coprime orders, so are trivial;
the existing three-centralizer factorization gives the result.

The application to the odd core imposes no solvability assumption on the
ambient group. This is the odd-core step in Aschbacher--Smith E.2.7,
printed p.220, for an all-c₂ symplectic pair.
-/
public section
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- An odd subgroup normalized by a noncyclic elementary two-group is trivial
when its three involution fixed subgroups are two-groups. -/
theorem eq_bot_of_odd_of_noncyclic_elementary_centralizers
    (P E : Subgroup G) [IsElementaryAbelian 2 E]
    (hodd : Odd (Nat.card P)) (hE : 2 < Nat.card E)
    (hEP : E ≤ normalizer (P : Set G))
    (hC : ∀ e ∈ E, e ≠ 1 → IsPGroup 2 (centralizer ({e} : Set G))) : P = ⊥ := by
  have square (e : E) : e ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E) e
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a,ha⟩ := exists_ne (1 : E)
  obtain ⟨b,hb,hba⟩ := ENat.exists_ne_ne_of_three_le (α := E)
    (by rw [ENat.card_eq_coe_natCard]; exact_mod_cast (by omega : 3 ≤ Nat.card E)) 1 a
  have hab : a * b ≠ 1 := by
    intro he
    apply hba
    exact (eq_inv_of_mul_eq_one_right he).trans
      (inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using square a))
  have hfix (e : E) (he : e ≠ 1) : P ⊓ centralizer ({(e : G)} : Set G) ≤ ⊥ := by
    obtain ⟨n,hn⟩ := (hC e e.property (fun hh => he (Subtype.ext hh))).exists_card_eq
    exact (disjoint_of_coprime_natCard (by
      rw [hn]
      exact hodd.coprime_two_right.pow_right n)).eq_bot.le
  let f : E →* normalizer (P : Set G) := inclusion hEP
  apply bot_unique
  apply le_of_three_odd_centralizers P ⊥ hodd (f a) (f b)
    (by rw [←map_pow,square,map_one]) (by rw [←map_pow,square,map_one])
    ((show Commute a b from (IsMulCommutative.is_comm (M := E)).comm a b).map f)
  intro t ht
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl | rfl
  · exact hfix a ha
  · exact hfix b hb
  · exact hfix (a*b) hab

/-- Noncyclic elementary two-groups with two-group involution centralizers
force the ambient odd core to be trivial. -/
theorem pPrimeCore_eq_bot_of_noncyclic_elementary_centralizers
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : 2 < Nat.card E)
    (hC : ∀ e ∈ E, e ≠ 1 → IsPGroup 2 (centralizer ({e} : Set G))) :
    pPrimeCore 2 G = ⊥ :=
  eq_bot_of_odd_of_noncyclic_elementary_centralizers _ E
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card) hE le_normalizer_of_normal hC

end Subgroup
