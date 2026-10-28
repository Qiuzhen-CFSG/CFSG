module

public import Theory.ElementaryAbelian.AutomorphismCardEight
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Fintype.Perm

/-!
# Enlarging a point stabilizer on an elementary eight-group

An actual S₄ point stabilizer in Aut(E₈), together with any automorphism
moving that point, generates all of Aut(E₈). The stabilizer has prime index
seven in the group of order 168, so there is no proper intermediate group.
The conclusion is equality of action images, as well as an isomorphism to
the concrete PSL₃(2) model; it does not identify actions from orders alone.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 14.2.21, printed p.988, the G₂(2) and M₁₂ branches.
-/

namespace MulAut

/-- Containing an S₄ point stabilizer and moving its point forces the full
automorphism action on an elementary abelian group of order eight. -/
public theorem eq_top_of_elementaryEight_stabilizer_of_moves
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (A : Subgroup (MulAut E)) (z : E)
    (hS : Nonempty (MulAction.stabilizer (MulAut E) z ≃* Equiv.Perm (Fin 4)))
    (hSA : MulAction.stabilizer (MulAut E) z ≤ A)
    (hmoves : ∃ a ∈ A, a z ≠ z) : A = ⊤ := by
  have hcardS : Nat.card (MulAction.stabilizer (MulAut E) z) = 24 := by
    rw [Nat.card_congr hS.some.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin]
    decide
  have hindex : (MulAction.stabilizer (MulAut E) z).index = 7 := by
    have h := (MulAction.stabilizer (MulAut E) z).card_mul_index
    rw [hcardS, card_mulAut_of_elementary_eight E hE] at h
    omega
  have hdvd : A.index ∣ 7 := hindex ▸ Subgroup.index_dvd_of_le hSA
  rcases (show Nat.Prime 7 by decide).eq_one_or_self_of_dvd _ hdvd with h | h
  · exact Subgroup.index_eq_one.mp h
  · have hrel := Subgroup.relIndex_mul_index hSA
    rw [h, hindex] at hrel
    have hAS : A ≤ MulAction.stabilizer (MulAut E) z :=
      Subgroup.relIndex_eq_one.mp (by omega)
    obtain ⟨a, ha, hmove⟩ := hmoves
    exact (hmove (hAS ha)).elim

/-- The full automorphism group of an elementary eight-group is the concrete
binary projective special linear group. -/
public theorem elementaryEight_equiv_PSL3
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) : Nonempty (MulAut E ≃* Matrix.PSL3Two.PSL) := by
  obtain ⟨e⟩ := elementaryEight_mulAut_equiv_GL E hE
  exact ⟨e.trans (Matrix.PSL3Two.equivGL.symm.trans Matrix.PSL3Two.equiv)⟩

end MulAut
