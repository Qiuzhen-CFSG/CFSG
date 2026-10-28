module

public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.GroupTheory.Fitting.Centralizer
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# A nontrivial two-core from a small three-core

In a solvable {2,3}-group with trivial two-core, the Fitting subgroup is the
three-core. Self-centralization and the Burnside basis-kernel theorem embed
the quotient by that core in the automorphism group of its Frattini quotient.
If the three-core has order at most 27, this is GL(d,3), d ≤ 3. None of its
possible orders is divisible by 64, nor is the order of the three-core.

This elementary solvable-group argument supplies a normal two-subgroup before
the defining-characteristic Borel–Tits argument in Aschbacher–Smith,
Proposition 1.3.4, printed p.511. It uses no classification of simple groups.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

private theorem no_sixtyfour_aut {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 3 E] (hE : Nat.card E ≤ 27) :
    ¬ 64 ∣ Nat.card (MulAut E) := by
  classical
  let n := Module.finrank (ZMod 3) (Additive E)
  have hc : Nat.card E = 3 ^ n := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive E)
    change Nat.card E = _ at hsize
    simpa only [Nat.card_zmod] using hsize
  have hn : n ≤ 3 := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 3) hh
    rw [← hc] at hp
    norm_num at hp
    omega
  let autLinear : MulAut E ≃* (Additive E ≃ₗ[ZMod 3] Additive E) :=
    { toFun := fun aut =>
        { aut.toAdditive with map_smul' := ZMod.map_smul aut.toAdditive }
      invFun := fun aut => MulEquiv.toAdditive.symm aut.toAddEquiv
      left_inv := by intro aut; ext; rfl
      right_inv := by intro aut; ext; rfl
      map_mul' := by intro aut other; ext; rfl }
  let b := Module.finBasis (ZMod 3) (Additive E)
  let e : MulAut E ≃* Matrix.GeneralLinearGroup (Fin n) (ZMod 3) :=
    autLinear.trans
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) (Additive E)).symm.trans
        (Matrix.GeneralLinearGroup.toLin' b).symm)
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  have hnum (k : ℕ) (hk : k ≤ 3) :
      ¬ 64 ∣ ∏ i : Fin k, (3 ^ k - 3 ^ (i : ℕ)) := by
    interval_cases k <;> norm_num [Fin.prod_univ_succ]
  simpa only [ZMod.card] using hnum n hn

/-- A solvable {2,3}-group whose three-core has order at most 27 and whose
order is divisible by 64 has a nontrivial two-core. -/
theorem twoCore_ne_bot_of_solvable_small_three_core {G : Type*} [Group G] [Finite G] (hs : Group.IsSolvable G)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p = 2 ∨ p = 3)
    (hsmall : Nat.card (pCore 3 G) ≤ 27) (hdiv : 64 ∣ Nat.card G) :
    pCore 2 G ≠ ⊥ := by
  intro htwo
  have hfit : fittingSubgroup G = pCore 3 G := by
    apply le_antisymm
    · rw [fitting_eq_sup_pCore]
      refine iSup_le fun p => ?_
      have hp := Nat.prime_of_mem_primeFactors p.val.property
      have hd := Nat.dvd_of_mem_primeFactors p.val.property
      rcases hprime p.val.val hp hd with he | he
      · rw [he, htwo]
        exact bot_le
      · rw [he]
    · exact pCore_le_fitting G 3
  have hcentral : centralizer (pCore 3 G : Set G) ≤ pCore 3 G := by
    rw [← hfit]
    exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs
  let N := pCore 3 G
  let _ : Fact (IsPGroup 3 N) := ⟨pCore_isPGroup⟩
  let V := N ⧸ frattini N
  let _ : IsElementaryAbelian 3 V := isElementaryAbelian_quotient_frattini (p := 3)
  let a : G →* MulAut V := (quotientAut (frattini N)).comp MulAut.conjNormal
  have hk : a.ker = N := pCore_frattini_action_kernel 3 hcentral
  have hc : Nat.card N * Nat.card a.range = Nat.card G := by
    rw [← index_ker, hk]
    exact N.card_mul_index
  have hcop : Nat.Coprime 64 (Nat.card N) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 3) (G := G)).exists_card_eq
    change Nat.Coprime 64 (Nat.card (pCore 3 G))
    rw [hn]
    exact (by decide : Nat.Coprime 64 3).pow_right n
  have h64 : 64 ∣ Nat.card (MulAut V) := by
    apply dvd_trans _ a.range.card_subgroup_dvd_card
    exact hcop.dvd_of_dvd_mul_left (hc ▸ hdiv)
  exact no_sixtyfour_aut
    ((Nat.le_of_dvd Nat.card_pos (card_quotient_dvd_card (frattini N))).trans hsmall) h64
