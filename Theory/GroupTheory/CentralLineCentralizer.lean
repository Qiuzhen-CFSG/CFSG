module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Centralizers of lines with central binary commutators

Commuting with a generator of an order-two subgroup defines a homomorphism
into the prescribed central line. Its kernel is the line centralizer, so
that centralizer has index at most two in the original group.

Source application: Aschbacher–Smith 13.7.4(2), 13.8.27, printed pp.936,963.
-/

public section
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Central line-valued commutators bound the actual relative centralizer index. -/
theorem line_centralizer_index_le_two (Q Z A : Subgroup G)
    (hZ : Nat.card Z = 2) (hA : Nat.card A = 2) (hAQ : A ≤ Q)
    (hcom : ⁅Q, A⁆ ≤ Z) (hcen : Z ≤ centralizer (Q : Set G)) :
    (Q ⊓ centralizer (A : Set G)).relIndex Q ≤ 2 := by
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 (hA ▸ dvd_rfl)
  have htG : orderOf (t : G) = 2 := (orderOf_injective A.subtype A.subtype_injective t).trans ht
  have hAt : A = zpowers (t : G) := (eq_of_le_of_card_ge (zpowers_le.mpr t.property)
    (by rw [Nat.card_zpowers, htG, hA])).symm
  let f : Q →* Z := {
    toFun q := ⟨⁅(q : G), (t : G)⁆, hcom (commutator_mem_commutator q.property t.property)⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' a b := by
      apply Subtype.ext
      change ⁅(a : G) * (b : G), (t : G)⁆ = ⁅(a : G), (t : G)⁆ * ⁅(b : G), (t : G)⁆
      have hb := hcom (commutator_mem_commutator b.property t.property)
      have hc := mem_centralizer_iff.mp (hcen hb) a a.property
      rw [commutatorElement_mul_left_eq_conj_mul, hc]
      simp only [mul_inv_cancel_right]
      have hd : ⁅(a : G), (t : G)⁆ ∈ Q :=
        le_normalizer_iff_commutator_le_left.mp Q.le_normalizer
          (commutator_mem_commutator a.property (hAQ t.property))
      exact (mem_centralizer_iff.mp (hcen hb) _ hd).symm }
  have hker : f.ker = (centralizer ({(t : G)} : Set G)).subgroupOf Q := by
    ext q
    change (⟨⁅(q : G), (t : G)⁆, _⟩ : Z) = 1 ↔ _
    rw [Subtype.ext_iff]
    change ⁅(q : G), (t : G)⁆ = 1 ↔ (q : G) ∈ centralizer ({(t : G)} : Set G)
    rw [commutatorElement_eq_one_iff_mul_comm, mem_centralizer_singleton_iff]
  rw [inf_relIndex_left, hAt, zpowers_eq_closure, centralizer_closure]
  change ((centralizer ({(t : G)} : Set G)).subgroupOf Q).index ≤ 2
  rw [← hker, index_ker]
  exact hZ ▸ Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective

end Subgroup
