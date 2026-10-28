module
public import Theory.SpecificGroups.GL2.ThreeConjugacy
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Four-groups in GL₂(3) are self-centralizing

A four-group contains an involution other than 1 and the scalar -I.
The checked conjugacy table puts this involution in the reflection class,
whose centralizer has order four. The abelian four-group therefore fills
its centralizer.

Source: the GL₂(3) conjugacy calculation in Wong (1964), article p.94,
and its use in Alperin–Brauer–Gorenstein, III.8 Proposition 5, p.117.
-/

open Matrix
namespace Matrix.GeneralLinearGroup
private abbrev G := GL (Fin 2) (ZMod 3)
private theorem central_commutes (a : G) : a * threeCentral = threeCentral * a := by
  apply Units.ext
  have h : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 3),
      A * threeCentral.val = threeCentral.val * A := by decide +kernel
  exact h a.val

/-- Every elementary abelian subgroup of order four in GL₂(3) is self-centralizing. -/
public theorem three_four_centralizer (T : Subgroup (GL (Fin 2) (ZMod 3)))
    [IsElementaryAbelian 2 T] (hT : Nat.card T = 4) :
    Subgroup.centralizer (T : Set (GL (Fin 2) (ZMod 3))) = T := by
  classical
  obtain ⟨y, hy, hy1, hyz⟩ : ∃ y ∈ T, y ≠ 1 ∧ y ≠ threeCentral := by
    by_contra hn
    have hall : (T : Set G) ⊆ {1, threeCentral} := by
      intro y hy
      by_cases h : y = 1
      · exact Or.inl h
      · exact Or.inr (Classical.byContradiction fun hz => hn ⟨y, hy, h, hz⟩)
    have hc := Set.ncard_mono hall
    rw [Set.ncard_pair (by decide : (1 : G) ≠ threeCentral),
      ← Nat.card_coe_set_eq] at hc
    change Nat.card T ≤ 2 at hc
    omega
  have hyorder : orderOf y = 2 := by
    apply orderOf_eq_prime_iff.mpr
    exact ⟨elemPow_eq_one_of_isElementaryAbelian y hy, hy1⟩
  obtain ⟨i, hi, -⟩ := three_conjugacy_data.1 y
  obtain ⟨g, hg⟩ := isConj_iff.mp hi
  let e := MulAut.conj g
  have he : e y = threeClassRepr i := hg
  have hio := e.orderOf_eq y
  rw [he] at hio
  rw [hyorder, three_conjugacy_data.2.1] at hio
  have hi15 : i = 1 ∨ i = 5 := by fin_cases i <;> simp_all
  have hi5 : i = 5 := by
    rcases hi15 with rfl | h
    · have hiy : IsConj y threeCentral := by simpa [threeClassRepr] using hi
      obtain ⟨g, hg⟩ := isConj_iff.mp hiy.symm
      apply False.elim
      apply hyz
      rw [central_commutes, mul_assoc, mul_inv_cancel, mul_one] at hg
      exact hg.symm
    · exact h
  subst i
  have hle : (Subgroup.centralizer (T : Set G)).map e.toMonoidHom ≤
      Subgroup.centralizer ({threeClassRepr 5} : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change e a * threeClassRepr 5 = threeClassRepr 5 * e a
    rw [← he]
    exact (map_mul e a y).symm.trans ((congrArg e (ha y hy).symm).trans (map_mul e y a))
  have hc := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective e.injective,
    three_conjugacy_data.2.2.1] at hc
  symm
  apply Subgroup.eq_of_le_of_card_ge T.le_centralizer
  change Nat.card (Subgroup.centralizer (T : Set G)) ≤ 4 at hc
  rw [hT]
  exact hc

end Matrix.GeneralLinearGroup
