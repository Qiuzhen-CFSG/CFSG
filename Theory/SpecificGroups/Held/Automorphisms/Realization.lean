module

public import Theory.SpecificGroups.Held.Automorphisms.Reduction
public import Theory.SpecificGroups.Held.Model.Transitivity
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedSubgroup
public import Theory.GroupAction.AutomorphismNormalizer

/-!
# Stabilizer route to realizing Held automorphisms

The literal ATLAS subgroup `M1` fixes the marked point. Transitivity gives
the point stabilizer index 2058, so an upper bound of 2058 for the index of
`M1` identifies it with that stabilizer. If an automorphism preserves the
conjugacy class of `M1`, the transitive-action transport theorem then realizes
it by a permutation normalizing the concrete Held group.

The index upper bound and the subgroup conjugacy assertion remain explicit
independent inputs. This module does not assert unconditional realization.
The final realization theorem must discharge both inputs.

Sources: Bray's ATLAS `HeG1-P1.M` specifies `M1` and its index 2058;
the representation is `HeG1-p2058B0`. GLS3, Table 5.3p records the full
outer group used on printed p.510 of Aschbacher--Smith, `refs/quasithin.pdf`.
-/

namespace Held.Realization

/-- The index calculation and the conjugacy calculation together realize
every automorphism in the full permutation normalizer. Neither missing
calculation is replaced by a presentation-isomorphism assumption. -/
public theorem normalizer_surjective_of_markedSubgroup
    (hindex : markedSubgroup.index ≤ 2058)
    (hconj : ∀ f : MulAut He, ∃ g : He,
      markedSubgroup.map f.toMonoidHom =
        markedSubgroup.map (MulAut.conj g).toMonoidHom) :
    Function.Surjective permutationGroup.normalizerMonoidHom := by
  have hstab := markedSubgroup_eq_baseStabilizer_of_index_le hindex
  intro f
  obtain ⟨g, hg⟩ := hconj f
  apply Subgroup.exists_normalizer_of_stabilizer_map_eq permutationGroup f
    basePoint (g • basePoint)
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  simpa only [hstab] using hg

end Held.Realization
