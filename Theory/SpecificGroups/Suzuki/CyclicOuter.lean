module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Cyclicity of the actual Suzuki outer group

The proved inner–field coverage makes the cyclic Galois group of the
defining field surject onto the quotient by inner automorphisms. This
strengthens the odd-index conclusion without any additional coverage premise.

Source: GLS3, Theorem 2.5.12(b–f), `refs/KGroup/GLS3/chapter2.tex`;
Aschbacher–Smith, proof of 13.6.6(ii), printed p.927.
-/

namespace BenderSuzuki.MatrixGroups

/-- The full outer automorphism group of a nondegenerate Suzuki group is cyclic. -/
public theorem suzuki_outer_isCyclic (m : ℕ) (hm : 1 ≤ m) :
    IsCyclic (MulAut.Outer (SuzukiMatrixGroup m)) := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (SuzukiMatrixGroup m))
  let f := q.comp (suzukiFieldAutHom m)
  apply isCyclic_of_surjective f
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨g, σ, rfl⟩ := suzukiAut_eq_inner_mul_field m hm a
  refine ⟨σ, ?_⟩
  have hg : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
  change q (suzukiFieldAutHom m σ) = _
  rw [map_mul, hg, one_mul, suzukiFieldAutHom_apply]

end BenderSuzuki.MatrixGroups
