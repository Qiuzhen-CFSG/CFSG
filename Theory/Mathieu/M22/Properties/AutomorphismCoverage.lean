module

public import Theory.Mathieu.M22.Properties.AutomorphismCoverage.Stabilizers
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage.Normalizer
public import Theory.Mathieu.M22.Properties.Automorphisms
public import Theory.GroupAction.AutomorphismNormalizer

/-!
# Full automorphism coverage for M₂₂

Every abstract automorphism preserves the index-22 point-stabilizer class,
so transitivity realizes it by a permutation normalizing the concrete M₂₂.
The normalizer preserves the hexads, recovered as involution fixed-point sets.
Its conjugation action is exactly the existing map `m22DesignAutToAut`.

This establishes the automorphism-group identification in GLS3, Table 5.3c,
Note 1. Together with the concrete index-two calculation it supplies the M₂₂
outer-group input used on printed p.510 of Aschbacher–Smith, combined manuscript
of 1 March 2004; M₂₂ occurs in the source list on printed p.33.
-/

namespace Sporadic.Mathieu

/-- Every abstract automorphism of M₂₂ is induced by a hexad-design automorphism. -/
public theorem m22DesignAutToAut_surjective :
    Function.Surjective m22DesignAutToAut := by
  let := m22_isPretransitive
  intro f
  obtain ⟨y, hy⟩ := m22_stabilizer_map_eq f (0 : Fin 22)
  obtain ⟨σ, hσ⟩ := Subgroup.exists_normalizer_of_stabilizer_map_eq M22 f 0 y hy
  refine ⟨⟨σ.val, m22_normalizer_le_designAut σ.property⟩, ?_⟩
  apply MulEquiv.ext
  intro t
  apply Subtype.ext
  rw [m22DesignAutToAut_apply_perm, ← hσ]
  rfl

end Sporadic.Mathieu
