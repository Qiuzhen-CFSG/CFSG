module

public import Theory.SpecificGroups.GL2.SemidihedralSylow
public import Theory.GroupTheory.SemidihedralStandardModel

/-!
# The GL2(3) Sylow comparison with SD16

The GL2 cardinality formula gives order 48 and Sylow two-order 16. Thus the
 general quadratic-torus semidihedral presentation has parameter four.
Recognition by that presentation and Sylow conjugacy give multiplicative
 equivalences from every actual Sylow two-subgroup to the standard SD16.

Source: Aschbacher–Smith, proof of 15.3.25, printed p.1133; the explicit
 GL2 presentation is supplied by `GL2.SemidihedralSylow`.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient.Conjugation

private theorem card_GL2_three : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
  rw [Matrix.card_GL_field]
  norm_num [Fin.prod_univ_two]

/-- The two-part of the actual matrix-group order is sixteen. -/
theorem card_GL2_three_sylow (P : Sylow 2 (GL (Fin 2) (ZMod 3))) : Nat.card P = 16 := by
  rw [P.card_eq_multiplicity, card_GL2_three]
  rw [show 48 = 16 * 3 by rfl, Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply]
  rw [show 16 = 2 ^ 4 by rfl, Nat.factorization_pow_self Nat.prime_two]
  norm_num [Nat.Prime.factorization Nat.prime_three]

/-- The order parameter in the general GL2 semidihedral presentation is four
 over the field with three elements. -/
theorem GL2_three_semidihedral_parameter (P : Sylow 2 (GL (Fin 2) (ZMod 3)))
    (n : ℕ) (hn : Nat.card P = 2 ^ n) : n = 4 := by
  have h : 2 ^ n = 2 ^ 4 := hn.symm.trans (card_GL2_three_sylow P)
  exact (Nat.pow_right_injective (by decide : 1 < 2)) h

/-- Every Sylow two-subgroup of GL2(3) is isomorphic to the standard SD16.
 The generators, not a family predicate, supply the multiplicative equivalence. -/
theorem GL2_three_sylow_equiv (Q : Sylow 2 (GL (Fin 2) (ZMod 3))) :
    Nonempty (Q ≃* Semidihedral.StandardModel 4 (by decide)) := by
  obtain ⟨P, n, hn, hP, a, b, ha, hb, hc, hgen, _, _⟩ :=
    Matrix.GeneralLinearGroup.exists_semidihedral_sylow (ZMod 3) (by
      norm_num [Nat.card_eq_fintype_card])
  have hn4 := GL2_three_semidihedral_parameter P n hP
  subst n
  obtain ⟨e⟩ := Semidihedral.standardModel_equiv_of_presentation hn a b ha hb hc hgen hP
  exact ⟨(Q.equiv P).trans e⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient.Conjugation

end
