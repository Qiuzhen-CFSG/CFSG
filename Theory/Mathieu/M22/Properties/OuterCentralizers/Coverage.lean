module

public import Theory.Mathieu.M22.Properties.OuterCentralizers.DesignAction
public import Theory.Mathieu.M22.Properties.ConjugateGeneration.EnumerationBridge
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Exhaustive fixed-point counts for outer M₂₂ involutions

The checked enumeration in `CubicInverters.Enumeration` exhausts an actual
Sylow two-subgroup of the full Steiner-design automorphism group. A kernel
check of its 256 permutation tables shows that every square-one element fixes
0, 6, 8, or 22 points. The tables are connected to the actual group elements by
`rowElement_apply`, and Sylow conjugacy covers every design involution.

An involution on 22 points with 6 or 22 fixed points is even, hence belongs to
M₂₂. The remaining possibilities for an outer involution are therefore 8 and 0.
This supplies the geometric coverage input for the two outer-centralizer rows
of Aschbacher–Smith 16.1.5(5), combined manuscript of 1 March 2004, printed
p.1171; the centralizer extension structures are separate calculations.
-/

public section

namespace Sporadic.Mathieu.M22OuterCentralizers
open Subgroup
open scoped Pointwise

private theorem fixedPoints_fintype_card (s : m22DesignAut) :
    Fintype.card (Function.fixedPoints s.val) = (fixedPoints s).card := by
  exact Fintype.card_of_finset' (p := Function.fixedPoints s.val) _
    (fun x => mem_fixedPoints s x)

private theorem fixedPoints_card_eq_sub_support (s : m22DesignAut) :
    (fixedPoints s).card = 22 - s.val.support.card := by
  rw [← fixedPoints_fintype_card, Equiv.Perm.card_fixedPoints,
    Equiv.Perm.sum_cycleType, Fintype.card_fin]

/-- Conjugating an actual design automorphism preserves its number of fixed points. -/
theorem fixedPoints_card_conj (g s : m22DesignAut) :
    (fixedPoints (g * s * g⁻¹)).card = (fixedPoints s).card := by
  rw [fixedPoints_card_eq_sub_support, fixedPoints_card_eq_sub_support]
  change 22 - (g.val * s.val * g.val⁻¹).support.card = _
  rw [Equiv.Perm.card_support_conj]

private theorem row_fixedPoints_cases (i : Fin 256) :
    (∃ x, M22CubicInverters.rowTable i (M22CubicInverters.rowTable i x) ≠ x) ∨
      (Finset.univ.filter fun x => M22CubicInverters.rowTable i x = x).card ∈
        ({0, 6, 8, 22} : Finset ℕ) := by
  revert i
  decide +kernel

private theorem fixedPoints_card_of_mem_standard (s : m22DesignAut)
    (hs : s ^ 2 = 1) (hmem : s ∈ M22CubicInverters.standardSylow) :
    (fixedPoints s).card ∈ ({0, 6, 8, 22} : Finset ℕ) := by
  obtain ⟨i, hi⟩ := M22CubicInverters.rowSylow_surjective ⟨s, hmem⟩
  have he : M22CubicInverters.rowElement i = s :=
    (M22ConjugateGeneration.rowSylow_val i).symm.trans (congrArg Subtype.val hi)
  subst s
  rcases row_fixedPoints_cases i with hbad | hcard
  · obtain ⟨x, hx⟩ := hbad
    have h := congrArg (fun g : m22DesignAut => g.val x) hs
    change (M22CubicInverters.rowElement i).val
      ((M22CubicInverters.rowElement i).val x) = x at h
    simp only [M22CubicInverters.rowElement_apply] at h
    exact (hx h).elim
  · simpa only [fixedPoints, M22CubicInverters.rowElement_apply] using hcard

private theorem involution_fixedPoints_cases (s : m22DesignAut) (hs : orderOf s = 2) :
    (fixedPoints s).card ∈ ({0, 6, 8, 22} : Finset ℕ) := by
  have hz : IsPGroup 2 (zpowers s) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq m22DesignAut Q M22CubicInverters.standardSylow
  let e : MulAut m22DesignAut := MulAut.conj g
  have hmem : e s ∈ M22CubicInverters.standardSylow := by
    rw [← hg]
    change e s ∈ (Q : Subgroup m22DesignAut).map e.toMonoidHom
    exact mem_map_of_mem e.toMonoidHom (hQ (mem_zpowers s))
  have hsq : (e s) ^ 2 = 1 := by
    have hord : orderOf (e s) = 2 := (e.orderOf_eq s).trans hs
    exact hord ▸ pow_orderOf_eq_one (e s)
  have hcard := fixedPoints_card_of_mem_standard (e s) hsq hmem
  simpa only [e, MulAut.conj_apply, fixedPoints_card_conj] using hcard

/-- Every outer involution in the faithful degree-22 design action fixes eight
points or no points. -/
theorem outer_involution_fixedPoints_card (s : m22DesignAut) (hs : orderOf s = 2)
    (ho : (s : Equiv.Perm (Fin 22)) ∉ M22) :
    (fixedPoints s).card = 8 ∨ (fixedPoints s).card = 0 := by
  have hsq : s.val ^ 2 = 1 := congrArg Subtype.val (hs ▸ pow_orderOf_eq_one s)
  have hsign := Equiv.Perm.sign_of_pow_two_eq_one hsq
  rw [fixedPoints_fintype_card, Fintype.card_fin] at hsign
  have heven : Equiv.Perm.sign s.val ≠ 1 := by
    intro h
    apply ho
    exact ⟨s.property, h⟩
  have hc := involution_fixedPoints_cases s hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with h0 | h6 | h8 | h22
  · exact Or.inr h0
  · rw [h6] at hsign
    exact (heven (hsign.trans (by decide))).elim
  · exact Or.inl h8
  · rw [h22] at hsign
    exact (heven (by simpa using hsign)).elim

end Sporadic.Mathieu.M22OuterCentralizers
