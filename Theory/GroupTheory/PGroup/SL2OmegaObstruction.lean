module
public import Theory.GroupTheory.PGroup.OmegaCoprimeAction
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Excluding SL₂ when prime-order automorphisms fix first omega

If all order-p automorphisms of a finite abelian p-group fix its first
omega subgroup, then its automorphism group contains no SL₂(p), for p > 2.
Transvections have p-th power one and generate SL₂, so any such image
lies in the p-group kernel of restriction to omega. The central involution
of SL₂ cannot lie in a p-group.

This supplies the final implication in Aschbacher–Smith, Lemma A.1.30,
printed p.27. The homocyclic automorphism calculation is a separate input.
-/

open Matrix Subgroup

private theorem transvection_pow_prime {p : ℕ} [Fact p.Prime]
    {i j : Fin 2} (hij : i ≠ j) (c : ZMod p) :
    SpecialLinearGroup.transvection hij c ^ p = 1 := by
  have hpow (n : ℕ) : SpecialLinearGroup.transvection hij c ^ n =
      SpecialLinearGroup.transvection hij (n • c) := by
    induction n with
    | zero => simp [SpecialLinearGroup.transvection_coeff_zero]
    | succ n ih =>
      rw [pow_succ, ih, ← SpecialLinearGroup.transvection_add, succ_nsmul]
  simpa [nsmul_eq_mul, SpecialLinearGroup.transvection_coeff_zero] using hpow p

/-- An SL₂(p) image contained in a p-subgroup cannot be faithful when p > 2. -/
public theorem not_injective_SL2_of_prime_order_mem_pSubgroup
    {p : ℕ} [Fact p.Prime] (hp : 2 < p) {G : Type*} [Group G]
    (K : Subgroup G) (hK : IsPGroup p K)
    (hmem : ∀ g : G, orderOf g = p → g ∈ K)
    (f : SpecialLinearGroup (Fin 2) (ZMod p) →* G) :
    ¬ Function.Injective f := by
  intro hf
  have hle (A : SpecialLinearGroup (Fin 2) (ZMod p)) : f A ∈ K := by
    apply SL2.transvection_induction (fun A => f A ∈ K) ?_ ?_ A
    · intro i j hij c
      have hpow : (f (SpecialLinearGroup.transvection hij c)) ^ p = 1 := by
        rw [← map_pow, transvection_pow_prime, map_one]
      by_cases he : f (SpecialLinearGroup.transvection hij c) = 1
      · exact he ▸ K.one_mem
      · exact hmem _ (orderOf_eq_prime_iff.mpr ⟨hpow, he⟩)
    · intro A B hA hB
      simpa only [map_mul] using K.mul_mem hA hB
  have hSL : IsPGroup p (SpecialLinearGroup (Fin 2) (ZMod p)) :=
    hK.of_injective (f.codRestrict K hle) (fun x y h => hf (congrArg Subtype.val h))
  let : Fact (2 < p) := ⟨hp⟩
  let : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩
  have hne : (-1 : SpecialLinearGroup (Fin 2) (ZMod p)) ≠ 1 := by
    intro h
    have hh := congrArg (fun A : SpecialLinearGroup (Fin 2) (ZMod p) => A.val 0 0) h
    exact ZMod.neg_one_ne_one (by simpa using hh)
  have hord : orderOf (-1 : SpecialLinearGroup (Fin 2) (ZMod p)) = 2 :=
    orderOf_eq_prime_iff.mpr ⟨by simp [pow_two], hne⟩
  have hc := hSL.orderOf_coprime
    ((Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr (by omega))
    (-1 : SpecialLinearGroup (Fin 2) (ZMod p))
  rw [hord] at hc
  norm_num at hc

/-- Fixation of first omega by order-p automorphisms excludes SL₂(p) from
the automorphism group of an abelian p-group. -/
public theorem not_injective_SL2_mulAut_of_prime_order_fixes_omega
    {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    {P : Type*} [Group P] [Finite P] [IsMulCommutative P] (hP : IsPGroup p P)
    (hfix : ∀ a : MulAut P, orderOf a = p → ∀ x ∈ omega₁ P (p := p), a x = x)
    (f : SpecialLinearGroup (Fin 2) (ZMod p) →* MulAut P) :
    ¬ Function.Injective f := by
  apply not_injective_SL2_of_prime_order_mem_pSubgroup hp
    (OmegaAction.omegaRestriction P p 1).ker (OmegaAction.restriction_kernel_isPGroup hP)
    (fun a ha => ?_) f
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  exact hfix a ha x x.property
