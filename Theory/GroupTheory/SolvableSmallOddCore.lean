module

public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.GroupTheory.Fitting.Centralizer
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# A nontrivial two-core from a small odd core

In a solvable group whose prime divisors are two and p, a trivial two-core
makes the p-core the self-centralizing Fitting subgroup. The Burnside basis
kernel theorem then embeds the quotient by the p-core in GL(n,p). The
explicit order bound below contradicts a specified two-power divisor.

This extends the elementary argument in `SolvableSmallThreeCore` and supplies
the intrinsic two-core used by the finite-model branches of Aschbacher–Smith,
Proposition 1.3.4, printed p.511.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

private theorem aut_not_dvd_of_elementary_card_bound {p d m : ℕ} [Fact p.Prime]
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian p E]
    (hE : Nat.card E ≤ p ^ d)
    (hnum : ∀ n ≤ d, ¬ m ∣ ∏ i : Fin n, (p ^ n - p ^ (i : ℕ))) :
    ¬ m ∣ Nat.card (MulAut E) := by
  classical
  let n := Module.finrank (ZMod p) (Additive E)
  have hc : Nat.card E = p ^ n := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive E)
    change Nat.card E = _ at hsize
    simpa only [Nat.card_zmod] using hsize
  have hn : n ≤ d := by
    rw [hc] at hE
    exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hE
  let autLinear : MulAut E ≃* (Additive E ≃ₗ[ZMod p] Additive E) :=
    { toFun := fun aut =>
        { aut.toAdditive with map_smul' := ZMod.map_smul aut.toAdditive }
      invFun := fun aut => MulEquiv.toAdditive.symm aut.toAddEquiv
      left_inv := by intro aut; ext; rfl
      right_inv := by intro aut; ext; rfl
      map_mul' := by intro aut other; ext; rfl }
  let b := Module.finBasis (ZMod p) (Additive E)
  let e : MulAut E ≃* Matrix.GeneralLinearGroup (Fin n) (ZMod p) :=
    autLinear.trans
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Additive E)).symm.trans
        (Matrix.GeneralLinearGroup.toLin' b).symm)
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  simpa only [ZMod.card] using hnum n hn

/-- The explicit small-dimensional general-linear orders force a nontrivial
two-core. The numerical bound is kept separate from the group argument. -/
theorem twoCore_ne_bot_of_solvable_small_odd_core {G : Type*} [Group G] [Finite G]
    {p d t : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hs : Group.IsSolvable G)
    (hprime : ∀ q : ℕ, q.Prime → q ∣ Nat.card G → q = 2 ∨ q = p)
    (hsmall : Nat.card (pCore p G) ≤ p ^ d) (hdiv : 2 ^ t ∣ Nat.card G)
    (hnum : ∀ n ≤ d, ¬ 2 ^ t ∣ ∏ i : Fin n, (p ^ n - p ^ (i : ℕ))) :
    pCore 2 G ≠ ⊥ := by
  intro htwo
  have hfit : fittingSubgroup G = pCore p G := by
    apply le_antisymm
    · rw [fitting_eq_sup_pCore]
      refine iSup_le fun q => ?_
      have hq := Nat.prime_of_mem_primeFactors q.val.property
      have hd := Nat.dvd_of_mem_primeFactors q.val.property
      rcases hprime q.val.val hq hd with he | he
      · rw [he, htwo]
        exact bot_le
      · rw [he]
    · exact pCore_le_fitting G p
  have hcentral : centralizer (pCore p G : Set G) ≤ pCore p G := by
    rw [← hfit]
    exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs
  let N := pCore p G
  let _ : Fact (IsPGroup p N) := ⟨pCore_isPGroup⟩
  let V := N ⧸ frattini N
  let _ : IsElementaryAbelian p V := isElementaryAbelian_quotient_frattini (p := p)
  let a : G →* MulAut V := (quotientAut (frattini N)).comp MulAut.conjNormal
  have hk : a.ker = N := pCore_frattini_action_kernel p hcentral
  have hc : Nat.card N * Nat.card a.range = Nat.card G := by
    rw [← index_ker, hk]
    exact N.card_mul_index
  have hcop : Nat.Coprime (2 ^ t) (Nat.card N) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := G)).exists_card_eq
    change Nat.Coprime (2 ^ t) (Nat.card (pCore p G))
    rw [hn]
    exact (Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime) |>.mpr hp.symm).pow t n
  have hdivAut : 2 ^ t ∣ Nat.card (MulAut V) := by
    apply dvd_trans _ a.range.card_subgroup_dvd_card
    exact hcop.dvd_of_dvd_mul_left (hc ▸ hdiv)
  exact aut_not_dvd_of_elementary_card_bound
    ((Nat.le_of_dvd Nat.card_pos (card_quotient_dvd_card (frattini N))).trans hsmall)
    hnum hdivAut
