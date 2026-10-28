module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.Model
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.IsPerfect

/-!
# A proper perfect subgroup of the actual Held fixed subgroup

The (5,7,6) relations force both generator images in every abelian quotient
to be trivial: the product has order dividing 35 and 6, and then each
generator has order dividing 5 and 7. This proves perfectness without an
order computation or an abstract covering-group identification.

The subgroup is proper because it centralizes `(a * bray)⁷`, whereas the
fixed element `a` does not. Source: the concrete relations in `Generators`,
for the triple-cover part of GLS3 Table 5.3p, outer 2C row.
-/

public section
open Subgroup
namespace Held.OuterInvolution.FixedStructure

private theorem triangle_abelian_trivial {A : Type*} [CommGroup A]
    (x y : A) (hx : x ^ 5 = 1) (hy : y ^ 7 = 1)
    (hxy : (x * y) ^ 6 = 1) : x = 1 ∧ y = 1 := by
  have h35 : (x * y) ^ 35 = 1 := by
    rw [mul_pow]
    have hx35 : x ^ 35 = 1 := by
      rw [show 35 = 5 * 7 from rfl, pow_mul, hx, one_pow]
    have hy35 : y ^ 35 = 1 := by
      rw [show 35 = 7 * 5 from rfl, pow_mul, hy, one_pow]
    rw [hx35, hy35, one_mul]
  have hprod : x * y = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_one
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h35)
      (orderOf_dvd_of_pow_eq_one hxy)
  have hx7 : x ^ 7 = 1 := by
    calc
      x ^ 7 = (x * y) ^ 7 := by rw [mul_pow, hy, mul_one]
      _ = 1 := by rw [hprod, one_pow]
  have hx1 : x = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_one
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx)
      (orderOf_dvd_of_pow_eq_one hx7)
  exact ⟨hx1, by simpa only [hx1, one_mul] using hprod⟩

/-- The two checked generators have trivial images in every abelian group. -/
theorem candidate_hom_to_commGroup_trivial {A : Type*} [CommGroup A]
    (f : candidate →* A) (g : candidate) : f g = 1 := by
  obtain ⟨hx, hy⟩ := triangle_abelian_trivial (f firstGenerator) (f secondGenerator)
    (by simpa using congrArg f firstGenerator_pow)
    (by simpa using congrArg f secondGenerator_pow)
    (by simpa using congrArg f productGenerator_pow)
  have hker : (⊤ : Subgroup candidate) ≤ f.ker := by
    rw [← closure_pair, Subgroup.closure_le]
    intro x hxmem
    rcases hxmem with rfl | hxmem
    · exact hx
    · exact Set.mem_singleton_iff.mp hxmem ▸ hy
  exact hker (Subgroup.mem_top g)

/-- Perfectness of the actual generated subgroup, with no cardinality premise. -/
instance candidate_perfect : Group.IsPerfect candidate where
  commutator_eq_top := by
    apply top_unique
    intro g _
    rw [← Abelianization.ker_of candidate]
    exact candidate_hom_to_commGroup_trivial Abelianization.of g

theorem candidate_le_center_word_centralizer :
    candidate ≤ centralizer ({(aFixed * brayFixed) ^ 7} : Set fixed) := by
  rw [candidate, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | hx
  · apply (mem_centralizer_singleton_iff (G := fixed)
      (g := (aFixed * brayFixed) ^ 7) (k := first)).mpr
    apply Subtype.ext
    exact first_commutes_center_word.eq
  · rw [Set.mem_singleton_iff] at hx
    subst x
    apply (mem_centralizer_singleton_iff (G := fixed)
      (g := (aFixed * brayFixed) ^ 7) (k := second)).mpr
    exact ((Commute.refl (aFixed * brayFixed)).pow_pow 12 7).eq

theorem aFixed_not_mem_candidate : aFixed ∉ candidate := by
  intro h
  have hc : aFixed * (aFixed * brayFixed) ^ 7 = (aFixed * brayFixed) ^ 7 * aFixed :=
    (mem_centralizer_singleton_iff (G := fixed)
      (g := (aFixed * brayFixed) ^ 7) (k := aFixed)).mp
        (candidate_le_center_word_centralizer h)
  apply a_not_commutes_center_word
  change a * (a * bray) ^ 7 = (a * bray) ^ 7 * a
  have he := congrArg fixed.subtype hc
  simpa only [map_mul, map_pow, Subgroup.subtype_apply, aFixed, brayFixed] using he

/-- Properness is certified by an actual element of the literal fixed subgroup. -/
theorem candidate_ne_top : candidate ≠ ⊤ := by
  intro h
  apply aFixed_not_mem_candidate
  rw [h]
  exact mem_top aFixed

end Held.OuterInvolution.FixedStructure
