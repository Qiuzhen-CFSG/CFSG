module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Parameters


/-!
# Polynomial root operators and invariant subspaces

A root expansion records the finite polynomial action of each actual root
subgroup on a rational representation. Every coefficient preserves every
invariant subspace: compose with a covector annihilating that subspace and use
uniqueness of a polynomial over the infinite ground field.

`HasShortRootDensity` is the precise remaining basic-module input: the
first-degree coefficients at short roots generate the full endomorphism
algebra. It is a condition, not an assertion that density has been proved.
Construction of root expansions from rationality is also left to consumers.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), Theorem 5.1 and the short-root ideal argument in 11.1(1).
-/

public section

open Theory.AlgebraicGroup
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
universe u v
variable {F : Type u} [Field F] [IsAlgClosed F]
variable {V : Type v} [AddCommGroup V] [Module F V]

/-- A finite polynomial expansion of each root action, with coefficients that
are actual endomorphisms of the representation space. -/
structure RootExpansion
    (ρ : RationalRepresentation (F4Chevalley.Carrier (k := F)) V) where
  coeff : F4Chevalley.Root → ℕ →₀ Module.End F V
  eval_eq : ∀ r t, (coeff r).sum (fun n A => t ^ n • A) =
    (ρ.action (algebraicRootElement r t)).val

private lemma coefficient_mem_of_eval_mem (p : ℕ →₀ V) (W : Submodule F V)
    (h : ∀ t : F, p.sum (fun n v => t ^ n • v) ∈ W) (n : ℕ) : p n ∈ W := by
  classical
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  let q : Polynomial F := p.sum (fun i w => Polynomial.monomial i (φ w))
  have hq (t : F) : q.eval t = φ (p.sum (fun n v => t ^ n • v)) := by
    simp only [q, Finsupp.sum, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  have hzero : q = 0 := by
    apply Polynomial.funext
    intro t
    rw [hq, Polynomial.eval_zero]
    exact (Submodule.mem_dualAnnihilator φ).mp hφ _ (h t)
  have hc := congrArg (fun f : Polynomial F => f.coeff n) hzero
  by_cases hn : n ∈ p.support
  · simpa [q, Finsupp.sum, Polynomial.coeff_monomial, eq_comm, hn] using hc
  · simp [Finsupp.notMem_support_iff.mp hn]

/-- Every polynomial coefficient of a root action preserves a group-invariant
subspace; this also applies to the first-degree infinitesimal operator. -/
theorem RootExpansion.coeff_mem
    {ρ : RationalRepresentation (F4Chevalley.Carrier (k := F)) V}
    (p : RootExpansion ρ) (W : Submodule F V) (hW : IsInvariantSubmodule ρ W)
    (r : F4Chevalley.Root) (n : ℕ) {v : V} (hv : v ∈ W) : p.coeff r n v ∈ W := by
  let q : ℕ →₀ V := (p.coeff r).mapRange (fun A => A v) (LinearMap.zero_apply v)
  have hq (t : F) : q.sum (fun n w => t ^ n • w) =
      (ρ.action (algebraicRootElement r t)).val v := by
    rw [← p.eval_eq]
    change ((p.coeff r).mapRange (fun A => A v) (LinearMap.zero_apply v)).sum
      (fun n w => t ^ n • w) = _
    rw [Finsupp.sum_mapRange_index (fun i => smul_zero (t ^ i))]
    simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]
  exact coefficient_mem_of_eval_mem q W (fun t => by rw [hq]; exact hW _ v hv) n

/-- Short-root density is a statement about the first-degree coefficients of
the genuine root actions, not the whole tensor or its composition factors. -/
@[expose] def RootExpansion.HasShortRootDensity
    {ρ : RationalRepresentation (F4Chevalley.Carrier (k := F)) V}
    (p : RootExpansion ρ) : Prop :=
  Algebra.adjoin F (Set.range fun r : {r : F4Chevalley.Root // ¬ IsLongRoot r} =>
    p.coeff r.val 1) = ⊤

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
