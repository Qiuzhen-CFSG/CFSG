module

public import Theory.GroupTheory.PrimeRankWitness
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Cubic subgroups surviving an involutory kernel

Two elements of order three, in the two factors of a direct product, generate
an elementary abelian subgroup of order nine. A homomorphism whose kernel has
exponent dividing two is injective on this subgroup. The resulting subgroup
is constructed as a range, including its containment in the full product image.
This applies to scalar quotients of orthogonal central products without
requiring either factor to be simple or perfect.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, A.2.17, printed p.39. The orthogonal
centralizer geometry is a separate input to that application.
-/

public section

open scoped IsMulCommutative

namespace CubicProductQuotient

variable {A B G : Type*} [Group A] [Group B] [Group G]

/-- The product of the two cyclic subgroups, followed by the given map. -/
@[expose] def cubicMap (f : A × B →* G) (a : A) (b : B) :
    Subgroup.zpowers a × Subgroup.zpowers b →* G :=
  f.comp ((Subgroup.zpowers a).subtype.prodMap (Subgroup.zpowers b).subtype)

/-- Every element in the product of the two cubic cyclic groups has cube one. -/
theorem cubicMap_cube {a : A} {b : B}
    (ha : orderOf a = 3) (hb : orderOf b = 3)
    (x : Subgroup.zpowers a × Subgroup.zpowers b) : x ^ 3 = 1 := by
  apply Prod.ext <;> apply Subtype.ext
  · exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers x.1.property).trans
      (ha ▸ dvd_rfl))
  · exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers x.2.property).trans
      (hb ▸ dvd_rfl))

/-- An involutory kernel meets the cubic product trivially. -/
theorem cubicMap_injective (f : A × B →* G)
    (hker : ∀ x, f x = 1 → x ^ 2 = 1) {a : A} {b : B}
    (ha : orderOf a = 3) (hb : orderOf b = 3) :
    Function.Injective (cubicMap f a b) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  have h2 : x ^ 2 = 1 := by
    have h := hker (x.1, x.2) hx
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (Subtype.ext (congrArg Prod.snd h))
  have h3 := cubicMap_cube ha hb x
  simpa only [pow_succ, h2, one_mul] using h3

/-- The image contains an actual elementary abelian subgroup of order nine. -/
theorem exists_nine (f : A × B →* G)
    (hker : ∀ x, f x = 1 → x ^ 2 = 1)
    (a : A) (b : B) (ha : orderOf a = 3) (hb : orderOf b = 3) :
    ∃ E : Subgroup G, E ≤ f.range ∧ IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  let g := cubicMap f a b
  have hg := cubicMap_injective f hker ha hb
  have hE : IsElementaryAbelian 3 g.range := by
    refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
    rintro ⟨x, y, rfl⟩
    apply Subtype.ext
    change g y ^ 3 = 1
    rw [← map_pow, cubicMap_cube ha hb, map_one]
  refine ⟨g.range, ?_, hE, ?_⟩
  · rintro x ⟨y, rfl⟩
    exact ⟨(y.1, y.2), rfl⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hg).toEquiv,
      Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, ha, hb]

/-- The constructed subgroup gives three-rank at least two. -/
theorem rank_ge_two [Finite G] (f : A × B →* G)
    (hker : ∀ x, f x = 1 → x ^ 2 = 1)
    (a : A) (b : B) (ha : orderOf a = 3) (hb : orderOf b = 3) :
    2 ≤ primeRank 3 G := by
  obtain ⟨E, _, hE, hcard⟩ := exists_nine f hker a b ha hb
  let := hE
  let : CommGroup E := IsMulCommutative.instCommGroup
  exact primeRank_ge_of_elementary_embedding
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 3 E))
    hcard E.subtype E.subtype_injective

end CubicProductQuotient
