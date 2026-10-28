module

public import ABG.ChapterII.Section2.SemidihedralCentralizerSylow

/-!
# Eighth-order roots of involutions in a QD-group

If a semidihedral Sylow subgroup has order sixteen, every involution is the
fourth power of an element of order eight. Take the cyclic generator from
its semidihedral presentation and conjugate its fourth power to the prescribed
involution, using QD fusion.

This supplies the generator required by the principal-block section formulas
without imposing characteristic power or triviality of local odd cores.
Source: ABG II.1 Proposition 1 and III.2, notation before Proposition 2.
-/

namespace ABG
variable {G : Type*} [Group G]

/-- Every involution has a cyclic root of order eight. -/
public theorem IsQDGroup.exists_order_eight_fourth_eq
    (hQD : IsQDGroup G) (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hcard : Nat.card S = 16)
    (x : G) (hx : orderOf x = 2) :
    ∃ a : G, orderOf a = 8 ∧ a ^ 4 = x := by
  obtain ⟨n, _, hncard, a, _, ha, _⟩ := hS
  have hn : n = 4 := Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))
    (hncard.symm.trans hcard)
  subst n
  have ha8 : orderOf (a : G) = 8 := (Subgroup.orderOf_coe a).trans ha
  have ha4 : orderOf ((a : G) ^ 4) = 2 := by
    rw [orderOf_pow_of_dvd (by decide) (by rw [ha8]; decide), ha8]
  have hclass : HasElementConjugacyClassCount G 2 1 := by
    rcases hQD with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.2.1
  obtain ⟨_, _, _, hcov⟩ := hclass
  obtain ⟨i, hi⟩ := hcov ((a : G) ^ 4) ha4
  obtain ⟨j, hj⟩ := hcov x hx
  obtain ⟨g, hg⟩ := isConj_iff.mp (hi.trans ((Subsingleton.elim i j) ▸ hj.symm))
  refine ⟨MulAut.conj g a, (orderOf_injective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective a).trans ha8, ?_⟩
  rw [← map_pow]
  exact hg
end ABG
