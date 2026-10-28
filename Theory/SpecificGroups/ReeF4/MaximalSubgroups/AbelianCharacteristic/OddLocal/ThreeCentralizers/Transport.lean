module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Transport and normalizer obstructions for order-three centralizers

Choose a generator of an order-three subgroup and transport full centralizers
along conjugacy. If every order-three element is conjugate to that generator,
then a noncentral element of order three in its centralizer prevents the cyclic
subgroup from being normal: normality would place that element in the cyclic
subgroup, hence in the center of its centralizer. Conjugacy to the inverse
separately produces nontrivial normalizer action.

These are elementary group arguments, with no ambient simplicity, maximality,
order formula or splitting assumption. Their source application is the finite
Ree class in GLS3, Table 4.7.3A and its descent on printed pp.233–234,
`refs/KGroup/GLS3/chapter4.tex`.
-/

public section

namespace ReeF4.MaximalSubgroups.AbelianCharacteristic.OddLocal

open Subgroup

variable {G H : Type*} [Group G] [Group H]

private def centralizerEquiv (e : G ≃* H) (a : G) :
    centralizer ({a} : Set G) ≃* centralizer ({e a} : Set H) where
  toFun x := ⟨e x, mem_centralizer_singleton_iff.mpr (by
    rw [← map_mul, ← map_mul]
    exact congrArg e (mem_centralizer_singleton_iff.mp x.property))⟩
  invFun x := ⟨e.symm x, mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simpa using mem_centralizer_singleton_iff.mp x.property)⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by ext; simp

/-- Conjugacy of elements transports their full centralizer carriers. -/
theorem centralizers_equiv_of_isConj {a b : G} (h : IsConj a b) :
    Nonempty (centralizer ({a} : Set G) ≃* centralizer ({b} : Set G)) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact ⟨centralizerEquiv (MulAut.conj g) a⟩

/-- Choose an ambient generator of a subgroup of order three. -/
theorem exists_generator_of_card_three (A : Subgroup G) [Finite A]
    (hA : Nat.card A = 3) :
    ∃ a : G, orderOf a = 3 ∧ zpowers a = A := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic A := isCyclic_of_prime_card hA
  obtain ⟨a, ha⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic A)
  refine ⟨a, ?_, ?_⟩
  · exact (orderOf_injective A.subtype A.subtype_injective a).trans
      ((orderOf_eq_card_of_zpowers_eq_top ha).trans hA)
  · change zpowers (A.subtype a) = A
    rw [← MonoidHom.map_zpowers, ha, ← MonoidHom.range_eq_map, range_subtype]

/-- A noncentral order-three element in the centralizer obstructs normality
of the original cyclic subgroup if all order-three elements are conjugate. -/
theorem normalizer_ne_top_of_three_conjugacy
    (a : G) (hconj : ∀ b : G, orderOf b = 3 → IsConj a b)
    (hnoncentral : ∃ x y : centralizer ({a} : Set G),
      orderOf x = 3 ∧ x * y ≠ y * x) :
    normalizer (zpowers a : Set G) ≠ ⊤ := by
  intro htop
  let : (zpowers a).Normal := normalizer_eq_top_iff.mp htop
  obtain ⟨x, y, hx, hxy⟩ := hnoncentral
  have hx3 : orderOf (x : G) = 3 :=
    (orderOf_injective (centralizer ({a} : Set G)).subtype Subtype.val_injective x).trans hx
  obtain ⟨g, hg⟩ := isConj_iff.mp (hconj x hx3)
  have hxA : (x : G) ∈ zpowers a :=
    hg ▸ (inferInstance : (zpowers a).Normal).conj_mem a (mem_zpowers a) g
  have hy : (y : G) ∈ centralizer (zpowers a : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
    exact y.property
  exact hxy (Subtype.ext (hy x hxA))

/-- Conjugacy to the inverse gives nontrivial normalizer action on a cyclic
group of order three. No splitting of the normalizer extension is asserted. -/
theorem centralizer_ne_normalizer_of_inverse_conjugacy
    (a : G) (ha : orderOf a = 3) (hconj : IsConj a a⁻¹) :
    centralizer (zpowers a : Set G) ≠ normalizer (zpowers a : Set G) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hgN : g ∈ normalizer (zpowers a : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (g * a * g⁻¹) = zpowers a
    rw [hg, zpowers_inv]
  intro heq
  have hgC : g ∈ centralizer ({a} : Set G) := by
    rw [← centralizer_closure, ← zpowers_eq_closure, heq]
    exact hgN
  have hcomm := mem_centralizer_singleton_iff.mp hgC
  have hi : a⁻¹ = a := by
    rw [← hg, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have ha2 : a ^ 2 = 1 := by simpa only [pow_two, hi] using inv_mul_cancel a
  have hdiv : 3 ∣ 2 := ha ▸ orderOf_dvd_of_pow_eq_one ha2
  exact (by decide : ¬ 3 ∣ 2) hdiv

end ReeF4.MaximalSubgroups.AbelianCharacteristic.OddLocal
