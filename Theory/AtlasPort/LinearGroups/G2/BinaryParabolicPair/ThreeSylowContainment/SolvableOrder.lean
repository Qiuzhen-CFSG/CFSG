module

public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.ElementaryAbelian.AutomorphismLinearModelEight
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The two-core at order 288

A solvable group of order 288 has a nontrivial two-core. Otherwise its
odd core is self-centralizing and has order dividing nine. The automorphism
group of a group of order dividing nine has order dividing 48: the only
noncyclic case is the two-dimensional vector space over the field of three
elements. The kernel and image of conjugation would therefore make 288 divide
9 · 48, a contradiction.

This elementary Fitting argument supplies the binary G₂ Sylow-overgroup
obstruction in Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`).
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace Atlas.G2.BinaryParabolicPair.ThreeSylowContainment

private theorem elementaryNine_aut_card
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 3 E]
    (hcard : Nat.card E = 9) : Nat.card (MulAut E) = 48 := by
  classical
  have hpow : 3 ^ Module.finrank (ZMod 3) (Additive E) = 3 ^ 2 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive E)
    change Nat.card E = _ at hsize
    simpa only [Nat.card_zmod, hcard, show (3 : ℕ)^2 = 9 from rfl] using hsize.symm
  have hdim : Module.finrank (ZMod 3) (Additive E) = 2 :=
    Nat.pow_right_injective (by decide : 1 < 3) hpow
  let autLinear : MulAut E ≃* (Additive E ≃ₗ[ZMod 3] Additive E) :=
    { toFun := fun aut =>
        { aut.toAdditive with map_smul' := ZMod.map_smul aut.toAdditive }
      invFun := fun aut => MulEquiv.toAdditive.symm aut.toAddEquiv
      left_inv := by intro aut; ext; rfl
      right_inv := by intro aut; ext; rfl
      map_mul' := by intro aut other; ext; rfl }
  let basis := Module.finBasisOfFinrankEq (ZMod 3) (Additive E) hdim
  let coordinates := autLinear.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) (Additive E)).symm.trans
      (Matrix.GeneralLinearGroup.toLin' basis).symm)
  rw [Nat.card_congr coordinates.toEquiv, Matrix.card_GL_field]
  norm_num [Fin.prod_univ_two]

private theorem dvd_nine_cases {n : ℕ} (hd : n ∣ 9) : n = 1 ∨ n = 3 ∨ n = 9 := by
  have hn := Nat.le_of_dvd (by decide : 0 < 9) hd
  interval_cases n <;> norm_num at *

private theorem aut_card_dvd_fortyEight_of_card_dvd_nine
    (E : Type*) [Group E] [Finite E] (hc : Nat.card E ∣ 9) :
    Nat.card (MulAut E) ∣ 48 := by
  have hcases := dvd_nine_cases hc
  by_cases hcyc : IsCyclic E
  · let := hcyc
    rw [IsCyclic.card_mulAut]
    rcases hcases with h | h | h <;> rw [h] <;> decide
  · have hcard : Nat.card E = 9 := by
      rcases hcases with h | h | h
      · exact False.elim (hcyc (isCyclic_of_orderOf_eq_card (1 : E) (by simp [h])))
      · exact False.elim (hcyc (isCyclic_of_prime_card h))
      · exact h
    let : IsMulCommutative E := IsPGroup.isMulCommutative_of_card_eq_prime_sq
      (p := 3) hcard
    let : IsElementaryAbelian 3 E := {
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
        intro x
        apply orderOf_dvd_iff_pow_eq_one.mp
        have hx : orderOf x ∣ 9 := hcard ▸ orderOf_dvd_natCard x
        have hm := dvd_nine_cases hx
        rcases hm with h | h | h
        · rw [h]; decide
        · rw [h]
        · exact False.elim (hcyc (isCyclic_of_orderOf_eq_card x (h.trans hcard.symm)))) }
    rw [elementaryNine_aut_card E hcard]

/-- A solvable group of order 288 has a nonidentity normal two-subgroup. -/
theorem twoCore_ne_bot_of_card_288
    (K : Type*) [Group K] [Finite K] (hs : Group.IsSolvable K)
    (hc : Nat.card K = 288) : pCore 2 K ≠ ⊥ := by
  intro hb
  let O := pPrimeCore 2 K
  have hO : Nat.card O ∣ 9 := by
    have hd : Nat.card O ∣ 32 * 9 := by simpa [hc] using O.card_subgroup_dvd_card
    have hcop : Nat.Coprime (Nat.card O) 32 :=
      (pPrimeCore_coprime_card (p := 2) (G := K)).symm.pow_right 5
    exact hcop.dvd_of_dvd_mul_left hd
  let action : K →* MulAut O := MulAut.conjNormal
  have hker : action.ker ≤ O := by
    apply le_trans ?_ (centralizer_pPrimeCore_le_of_pCore_eq_bot 2 hs hb)
    intro g hg
    apply mem_centralizer_iff.mpr
    intro x hx
    have h := congrArg (fun f : MulAut O => (f ⟨x, hx⟩ : K)) hg
    change g * x * g⁻¹ = x at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have hk : Nat.card action.ker ∣ 9 := (card_dvd_of_le hker).trans hO
  have hr : Nat.card action.range ∣ 48 := action.range.card_subgroup_dvd_card.trans
    (aut_card_dvd_fortyEight_of_card_dvd_nine O hO)
  have hd := Nat.mul_dvd_mul hk hr
  rw [← index_ker, card_mul_index, hc] at hd
  norm_num at hd

end Atlas.G2.BinaryParabolicPair.ThreeSylowContainment
