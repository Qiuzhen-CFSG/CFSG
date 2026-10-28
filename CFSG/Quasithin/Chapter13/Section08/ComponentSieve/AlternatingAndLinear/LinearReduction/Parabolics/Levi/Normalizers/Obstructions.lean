module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.MarkedResiduals

/-!
# Four geometric obstructions to endpoint normalizer containment

Conjugating a node's cubic element by a basis permutation sends its two
marked coordinates to the permuted coordinates. If this crosses a retained
flag cut, the permutation cannot normalize the actual O² residual. Four
adjacent swaps exclude all unwanted nonadjacent ordered node pairs once
the two endpoint normalizer lower bounds have been established.

The cubic elements and their residual membership are the checked witnesses
from MarkedResiduals. No description of the full residual is assumed.
Source: Aschbacher–Smith, 13.8.25, combined manuscript of 1 March 2004,
printed p.960 (PDF p.977). The final helper retains its two explicit bounds.
-/

public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.SylowOvergroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

private theorem permutation_not_mem_normalizer (b : FiveBasis) (i k : Fin 4)
    (σ : Equiv.Perm (Fin 5)) (hki : k ≠ i)
    (hl : (σ i.castSucc).val ≤ k.val) (hr : k.val < (σ i.succ).val) :
    b.equiv b σ ∉ normalizer (fiveNodeResidual b i) := by
  intro hn
  have hc : b.equiv b σ * fiveNodeRotation b i * (b.equiv b σ)⁻¹ ∈
      fiveParabolic b {i} :=
    fiveNodeResidual_le b i ((hn _).mp (fiveNodeRotation_mem_residual b i))
  have hv := ((mem_flagStabilizer_iff b {i}ᶜ _).mp hc k hki
    (b (σ i.castSucc))).mpr ((basis_mem_flagSpace_iff b k _).mpr hl)
  have he : (b.equiv b σ)⁻¹ (b (σ i.castSucc)) = b i.castSucc := by
    apply (b.equiv b σ).injective
    simp
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, he,
    fiveNodeRotation_apply_left, Module.Basis.equiv_apply, basis_mem_flagSpace_iff] at hv
  exact Nat.not_le_of_gt hr hv

private theorem swap_mem_cut (b : FiveBasis) (r s : Fin 5) (k : Fin 4)
    (h : (r.val ≤ k.val ↔ s.val ≤ k.val)) :
    b.equiv b (Equiv.swap r s) ∈ flagStabilizer b {k} := by
  classical
  apply (mem_flagStabilizer_iff_maps b {k} _).mpr
  intro j hj
  have hjk : j = k := hj
  subst j
  have hle : flagSpace b k ≤ (flagSpace b k).comap
      (b.equiv b (Equiv.swap r s)).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, ht, rfl⟩
    change b.equiv b (Equiv.swap r s) (b t) ∈ flagSpace b k
    rw [Module.Basis.equiv_apply, basis_mem_flagSpace_iff]
    by_cases htr : t = r
    · subst t
      simpa using h.mp ht
    · by_cases hts : t = s
      · subst t
        simpa using h.mpr ht
      · simpa [Equiv.swap_apply_of_ne_of_ne htr hts] using ht
  exact fun v hv => hle hv

/-- Swapping the last two coordinates carries the third-node cubic across cut 3. -/
theorem twoSpace_not_le_nodeTwo_normalizer (b : FiveBasis) :
    ¬ flagStabilizer b {1} ≤ normalizer (fiveNodeResidual b 2) := by
  intro h
  exact permutation_not_mem_normalizer b 2 3 (Equiv.swap 3 4) (by decide)
    (by decide) (by decide) (h (swap_mem_cut b 3 4 1 (by decide)))

/-- Swapping coordinates 2 and 3 carries the last-node cubic across cut 2. -/
theorem twoSpace_not_le_nodeThree_normalizer (b : FiveBasis) :
    ¬ flagStabilizer b {1} ≤ normalizer (fiveNodeResidual b 3) := by
  intro h
  exact permutation_not_mem_normalizer b 3 2 (Equiv.swap 2 3) (by decide)
    (by decide) (by decide) (h (swap_mem_cut b 2 3 1 (by decide)))

/-- Swapping coordinates 1 and 2 carries the first-node cubic across cut 1. -/
theorem threeSpace_not_le_nodeZero_normalizer (b : FiveBasis) :
    ¬ flagStabilizer b {2} ≤ normalizer (fiveNodeResidual b 0) := by
  intro h
  exact permutation_not_mem_normalizer b 0 1 (Equiv.swap 1 2) (by decide)
    (by decide) (by decide) (h (swap_mem_cut b 1 2 2 (by decide)))

/-- Swapping the first two coordinates carries the second-node cubic across cut 0. -/
theorem threeSpace_not_le_nodeOne_normalizer (b : FiveBasis) :
    ¬ flagStabilizer b {2} ≤ normalizer (fiveNodeResidual b 1) := by
  intro h
  exact permutation_not_mem_normalizer b 1 0 (Equiv.swap 0 1) (by decide)
    (by decide) (by decide) (h (swap_mem_cut b 0 1 2 (by decide)))
/-- Only the two endpoint normalizer lower bounds are needed for the node sieve. -/
theorem fiveNodeResidual_normalizer_pair_of_endpoint_bounds (b : FiveBasis)
    (hfirst : flagStabilizer b {1} ≤ normalizer (fiveNodeResidual b 0))
    (hlast : flagStabilizer b {2} ≤ normalizer (fiveNodeResidual b 3))
    (beta delta : Fin 4)
    (hgap : beta.val + 1 < delta.val ∨ delta.val + 1 < beta.val)
    (hN : normalizer (fiveNodeResidual b beta : Set (LinearGroup 5)) ≤
      normalizer (fiveNodeResidual b delta : Set (LinearGroup 5))) :
    (beta = 2 ∧ delta = 0) ∨ (beta = 1 ∧ delta = 3) := by
  fin_cases beta <;> fin_cases delta <;> norm_num at hgap
  · exact (twoSpace_not_le_nodeTwo_normalizer b (hfirst.trans hN)).elim
  · exact (twoSpace_not_le_nodeThree_normalizer b (hfirst.trans hN)).elim
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact (threeSpace_not_le_nodeZero_normalizer b (hlast.trans hN)).elim
  · exact (threeSpace_not_le_nodeOne_normalizer b (hlast.trans hN)).elim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

end
