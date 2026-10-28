module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.Sylow

/-!
# Quaternion exclusion and order-four generators

A product of a dihedral group with an abelian group of exponent two has no
quaternion subgroup: its elements whose square is nonidentity are rotations
in the first factor, and therefore commute. Sylow conjugacy extends this
obstruction to any finite group with such a Sylow two-subgroup.

A separate generator lemma reduces Q₈ containment to its order-four elements.
These elementary tools support the outer-involution centralizer calculation
used by Aschbacher–Smith, proof of 16.4.9(2), printed p.1192.
-/

public section

open Subgroup
namespace QuaternionGroup
variable {G A : Type*} [Group G] [CommGroup A]

private theorem dihedral_prod_commute {n : ℕ} (hA : ∀ x : A, x ^ 2 = 1)
    (x y : DihedralGroup n × A) (hx : x ^ 2 ≠ 1) (hy : y ^ 2 ≠ 1) : Commute x y := by
  have hfst (z : DihedralGroup n × A) (hz : z ^ 2 ≠ 1) : z.1 ^ 2 ≠ 1 := by
    intro h
    exact hz (Prod.ext h (hA z.2))
  have hx' := hfst x hx
  have hy' := hfst y hy
  rcases x with ⟨i, u⟩
  rcases y with ⟨j, v⟩
  cases i with
  | sr i => exact (hx' (by simp [pow_two])).elim
  | r i =>
    cases j with
    | sr j => exact (hy' (by simp [pow_two])).elim
    | r j =>
      change (DihedralGroup.r i, u) * (DihedralGroup.r j, v) =
        (DihedralGroup.r j, v) * (DihedralGroup.r i, u)
      exact Prod.ext (by simp [add_comm]) (mul_comm u v)

/-- A dihedral group times an abelian group of exponent two contains no Q₈. -/
theorem not_injective_dihedral_prod {n : ℕ} (hA : ∀ x : A, x ^ 2 = 1)
    (f : QuaternionGroup 2 →* DihedralGroup n × A) : ¬ Function.Injective f := by
  intro hf
  have ha : f (a 1) ^ 2 ≠ 1 := by
    intro h
    have hh : (a 1 : QuaternionGroup 2) ^ 2 = 1 := hf (by simpa only [map_pow, map_one] using h)
    exact (by decide : (a 1 : QuaternionGroup 2) ^ 2 ≠ 1) hh
  have hb : f (xa 0) ^ 2 ≠ 1 := by
    intro h
    have hh : (xa 0 : QuaternionGroup 2) ^ 2 = 1 := hf (by simpa only [map_pow, map_one] using h)
    exact (by decide : (xa 0 : QuaternionGroup 2) ^ 2 ≠ 1) hh
  have hh : (a 1 : QuaternionGroup 2) * xa 0 = xa 0 * a 1 :=
    hf (by simpa only [map_mul] using (dihedral_prod_commute hA _ _ ha hb).eq)
  exact (by decide : (a 1 : QuaternionGroup 2) * xa 0 ≠ xa 0 * a 1) hh

/-- The order-four elements generate every quaternion subgroup of order eight. -/
theorem subgroup_le_of_order_four (P K : Subgroup G) (e : P ≃* QuaternionGroup 2)
    (hfour : ∀ x ∈ P, orderOf x = 4 → x ∈ K) : P ≤ K := by
  let f : QuaternionGroup 2 →* G := P.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := P.subtype_injective.comp e.symm.injective
  have ha : f (a 1) ∈ K := hfour _ (e.symm (a 1)).property (by
    rw [orderOf_injective f hf, orderOf_a_one])
  have hb : f (xa 0) ∈ K := hfour _ (e.symm (xa 0)).property (by
    rw [orderOf_injective f hf, orderOf_xa])
  intro x hx
  have he : f (e ⟨x, hx⟩) = x := by simp [f]
  rw [← he]
  cases e ⟨x, hx⟩ with
  | a i =>
    have hi : (a i : QuaternionGroup 2) = a 1 ^ i.val := by simp
    rw [hi, map_pow]
    exact K.pow_mem ha _
  | xa i =>
    have hi : (xa i : QuaternionGroup 2) = xa 0 * a 1 ^ i.val := by simp
    rw [hi, map_mul, map_pow]
    exact K.mul_mem hb (K.pow_mem ha _)

/-- A finite group with a dihedral times exponent-two Sylow subgroup contains no Q₈. -/
theorem not_injective_of_sylow_dihedral_prod [Finite G] {n : ℕ}
    (S : Sylow 2 G) (e : S ≃* DihedralGroup n × A)
    (hA : ∀ x : A, x ^ 2 = 1) (f : QuaternionGroup 2 →* G) :
    ¬ Function.Injective f := by
  intro hf
  have hq : IsPGroup 2 (QuaternionGroup 2) :=
    IsPGroup.of_card (n := 3) (by simp [Nat.card_eq_fintype_card, card])
  have hp : IsPGroup 2 f.range := hq.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  let j : f.range →* T := Subgroup.inclusion hT
  let k := e.toMonoidHom.comp ((T.equiv S).toMonoidHom.comp (j.comp f.rangeRestrict))
  exact not_injective_dihedral_prod hA k
    (e.injective.comp ((T.equiv S).injective.comp
      ((Subgroup.inclusion_injective hT).comp (by
        intro x y h
        exact hf (congrArg Subtype.val h)))))
end QuaternionGroup
