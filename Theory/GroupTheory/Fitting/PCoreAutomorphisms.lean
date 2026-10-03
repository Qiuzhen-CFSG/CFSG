module

public import Theory.GroupTheory.Fitting.Centralizer

/-!
# Solvable groups controlled by automorphisms of their prime core

If a finite solvable group has trivial prime-complement core and its prime
core has a prime-power automorphism group, then the whole group is a p-group.
The Fitting subgroup equals the prime core and is self-centralizing.
Consequently both the kernel and image of conjugation on the prime core
are p-groups.

This combines Fitting self-centralization with the elementary extension
property for p-groups; see Huppert III, the Fitting subgroup discussion.
-/

/-- In a solvable group with trivial p-prime core, a p-group automorphism
group of the p-core forces the ambient group to be a p-group. -/
public theorem isPGroup_of_pPrimeCore_eq_bot_of_mulAut_pCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hsolv : Group.IsSolvable G) (hcore : pPrimeCore p G = ⊥)
    (haut : IsPGroup p (MulAut (pCore p G))) : IsPGroup p G := by
  let P := pCore p G
  let action : G →* MulAut P := MulAut.conjNormal
  have hker : action.ker ≤ P := by
    have hfit := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
    rw [Fitting_eq_pcore G p hcore] at hfit
    apply le_trans ?_ hfit
    intro g hg
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    have h := congrArg (fun f : MulAut P => (f ⟨x, hx⟩ : G)) hg
    change g * x * g⁻¹ = x at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have hk : IsPGroup p action.ker := (pCore_isPGroup (p := p) (G := G)).to_le hker
  have ht := (haut.to_subgroup ⊤).comap_of_ker_isPGroup action hk
  rw [Subgroup.comap_top] at ht
  exact ht.of_equiv Subgroup.topEquiv
