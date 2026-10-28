module
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.Model
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.FixedOrderBound.Support
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Noninner
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.OrbitalPreservation

/-!
# From the graph centralizer to the literal fixed subgroup

The faithful Held representation embeds every fixed element in the graph
centralizer of the actual outer involution. Held's perfectness makes that image
even, whereas the involution itself is odd and preserves the graph. The image
is therefore proper, and the subgroup index formula halves the graph bound.
Source: GLS3 Table 5.3p, outer 2C row, in the fixed ATLAS degree-2058 model.
-/

namespace Held.OuterInvolution.FixedStructure.FixedOrderBound
open Held.NormalizerGraph

private theorem representation_mem (g : fixed) : representation g.val ∈ graphCentralizer := by
  refine ⟨Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup
    g.val.property, ?_⟩
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hf : action g.val = g.val := (MulAut.mem_fixedSubgroup action g.val).mp g.property
  have he := congrArg representation hf
  rw [representation_action] at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

private def fixedEmbedding : fixed →* graphCentralizer where
  toFun g := ⟨representation g.val, representation_mem g⟩
  map_one' := Subtype.ext (map_one representation)
  map_mul' g h := Subtype.ext (map_mul representation g.val h.val)

private theorem fixedEmbedding_injective : Function.Injective fixedEmbedding := by
  intro g h he
  have hv : representation g.val = representation h.val :=
    congrArg (fun p : graphCentralizer => p.val) he
  exact Subtype.ext (representation_injective hv)

public theorem fixed_card_le_of_graph_bound (hbound : Nat.card graphCentralizer ≤ 30240) :
    Nat.card fixed ≤ 15120 := by
  have ht : involution ∈ graphCentralizer := by
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    exact Orbital.normalizer_le_of_invariant
      Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup
      representative.property
  have hproper : fixedEmbedding.range ≠ ⊤ := by
    intro he
    have hm : (⟨involution, ht⟩ : graphCentralizer) ∈ fixedEmbedding.range :=
      he ▸ Subgroup.mem_top _
    obtain ⟨g, hg⟩ := hm
    have hsign := hom_to_commGroup_trivial (Equiv.Perm.sign.comp representation) g.val
    have heq : representation g.val = involution := congrArg Subtype.val hg
    simp only [MonoidHom.comp_apply] at hsign
    rw [heq] at hsign
    have hn : Equiv.Perm.sign involution = -1 := representative_sign
    rw [hn] at hsign
    exact (by decide : (-1 : ℤˣ) ≠ 1) hsign
  have hindex : 2 ≤ fixedEmbedding.range.index :=
    fixedEmbedding.range.one_lt_index_of_ne_top hproper
  have hcard : Nat.card fixedEmbedding.range = Nat.card fixed :=
    (Nat.card_congr (MonoidHom.ofInjective fixedEmbedding_injective).toEquiv).symm
  have hmul := fixedEmbedding.range.card_mul_index
  rw [hcard] at hmul
  have hle : Nat.card fixed * 2 ≤ Nat.card graphCentralizer := by
    rw [← hmul]
    exact Nat.mul_le_mul_left _ hindex
  omega
end Held.OuterInvolution.FixedStructure.FixedOrderBound
