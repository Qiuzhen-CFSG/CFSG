module

public import Theory.SpecificGroups.PSL4Three.ProperOvergroups.IrreducibleMaximals.Data
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Theory.GroupTheory.TwoThreeSolvable

/-!
# Prime-order seeds for nonsolvable subgroups of PSL₄(3)

The quotient SL₄(3) → PSL₄(3) and the embedding SL₄(3) → GL₄(3)
show that every subgroup order divides
`|GL₄(3)| = 24261120 = 2^9 * 3^6 * 5 * 13`.
The two-prime solvability theorem excludes support contained in {2,3}
for a nonsolvable subgroup. Cauchy's theorem then supplies an actual
element of order five or thirteen inside that subgroup.

Only the divisibility bound is needed; no maximal-subgroup classification
or simplicity assertion enters this argument.

Source application: Aschbacher–Smith, Theorem 0.1.2(4) and condition K,
printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

namespace Matrix.PSL4Three.ProperOvergroups.IrreducibleMaximals

/-- Every projective subgroup order divides the order of the general linear group. -/
public theorem card_dvd_GL_order (U : Subgroup PSL) : Nat.card U ∣ 24261120 := by
  have hGL : Nat.card (GL (Fin 4) (ZMod 3)) = 24261120 := by
    rw [card_GL_field]
    norm_num [Fin.prod_univ_succ]
  rw [← hGL]
  exact U.card_subgroup_dvd_card.trans
    ((Subgroup.card_dvd_of_surjective project (QuotientGroup.mk'_surjective _)).trans
      (Subgroup.card_dvd_of_injective SpecialLinearGroup.toGL
        SpecialLinearGroup.toGL_injective))

/-- The four possible prime divisors of a projective subgroup order. -/
public theorem prime_dvd_card (U : Subgroup PSL) (p : ℕ) (hp : p.Prime)
    (h : p ∣ Nat.card U) : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 13 := by
  have hd := h.trans (card_dvd_GL_order U)
  have he : 24261120 = 2 ^ 9 * 3 ^ 6 * 5 * 13 := by decide
  rw [he] at hd
  rcases hp.dvd_mul.mp hd with hd | hd
  · rcases hp.dvd_mul.mp hd with hd | hd
    · rcases hp.dvd_mul.mp hd with hd | hd
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hd)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp hd)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13)).mp hd)))

/-- Nonsolvability produces an actual element of order five or thirteen. -/
public theorem five_or_thirteen_of_nonsolvable
    (U : Subgroup PSL) (hU : ¬ Group.IsSolvable U) :
    (∃ x : U, orderOf x = 5) ∨ ∃ x : U, orderOf x = 13 := by
  classical
  have hd : 5 ∣ Nat.card U ∨ 13 ∣ Nat.card U := by
    by_contra hn
    push Not at hn
    apply hU (Theory.GroupTheory.isSolvable_of_prime_dvd_card_eq_two_or_three U ?_)
    intro p hp hpd
    rcases prime_dvd_card U p hp hpd with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact False.elim (hn.1 hpd)
    · exact False.elim (hn.2 hpd)
  rcases hd with h5 | h13
  · let : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact Or.inl (exists_prime_orderOf_dvd_card' 5 h5)
  · let : Fact (Nat.Prime 13) := ⟨by decide⟩
    exact Or.inr (exists_prime_orderOf_dvd_card' 13 h13)

end Matrix.PSL4Three.ProperOvergroups.IrreducibleMaximals
