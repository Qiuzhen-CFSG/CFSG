module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.RankSixCertificate.Data
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.SextetStabilizer.GraphBound
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound.Odd

/-!
# Ambient bounds from the fixed sextets of the Held rows

A subgroup normalizer preserves its fixed-point set. The two literal rows
therefore have normalizers inside their actual sextet stabilizers. The published
odd symmetry of the Held graph takes the row-20 sextet to the row-21 sextet.
Conjugating permutations by this symmetry embeds either graph-preserving sextet
stabilizer in the already certified group of order at most 138240.

We use only the symmetry's graph preservation, not an identification of it as
an automorphism of Held. Source: GLS3 Table 5.3p and the original ATLAS carrier;
the graph symmetry is retained in `InnerNormalizer/Source/odd.json`.
-/

public section
open scoped Pointwise
namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.RankSixCertificate
open Subgroup
open LocalPairs.SylowGeometry.Calculations.InnerNormalizer
open LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient

/-- The ambient Held stabilizer of the six actual fixed vertices. -/
@[expose] def sextetStabilizer (k : Fin 2) : Subgroup He :=
  (MulAction.stabilizer (Equiv.Perm (Fin 2058))
    (sextet k : Set (Fin 2058))).comap representation

private theorem normalizer_preserves_fixedPoints {G X : Type*} [Group G] [MulAction G X]
    (U : Subgroup G) (g : G) (hg : g ∈ normalizer (U : Set G))
    (x : X) (hx : x ∈ MulAction.fixedPoints U X) :
    g • x ∈ MulAction.fixedPoints U X := by
  intro p
  have hp : g⁻¹ * p.val * g ∈ U := by
    simpa using (mem_normalizer_iff.mp ((normalizer (U : Set G)).inv_mem hg) p.val).mp
      p.property
  have he := hx (⟨g⁻¹ * p.val * g, hp⟩ : U)
  change (g⁻¹ * p.val * g) • x = x at he
  change p.val • (g • x) = g • x
  simpa only [mul_smul, smul_inv_smul] using congrArg (g • ·) he

/-- This is an ambient containment, obtained from the exact fixed-point calculation. -/
theorem normalizer_le_sextetStabilizer (k : Fin 2) :
    normalizer (ambient (row k) : Set He) ≤ sextetStabilizer k := by
  intro g hg
  apply MulAction.mem_stabilizer_set.mpr
  intro x
  rw [← fixedPoints_eq]
  constructor
  · intro hx
    simpa only [inv_smul_smul] using
      normalizer_preserves_fixedPoints _ g⁻¹ (inv_mem hg) (g • x) hx
  · exact normalizer_preserves_fixedPoints _ g hg x

private def transport (k : Fin 2) : Equiv.Perm (Fin 2058) :=
  if k = 0 then GraphBound.oddPermutation else 1

private theorem transport_graph (k : Fin 2) : transport k ∈ NormalizerGraph.preservingGroup := by
  fin_cases k
  · exact GraphBound.odd_mem.1
  · exact one_mem _

private theorem transport_sextet (k : Fin 2) :
    (sextet k).image (transport k) = Max3.sextet := by
  fin_cases k <;> decide +kernel

private theorem transport_mem (k : Fin 2) (x : Fin 2058) :
    transport k x ∈ Max3.sextet ↔ x ∈ sextet k := by
  rw [← transport_sextet k]
  constructor
  · rintro hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    exact (transport k).injective he ▸ hy
  · exact Finset.mem_image_of_mem _

private theorem transported_mem_graphSextetGroup
    (hgraph : permutationGroup ≤ NormalizerGraph.preservingGroup)
    (k : Fin 2) (g : sextetStabilizer k) :
    (MulAut.conj (transport k)) (representation g.val) ∈ Max3.graphSextetGroup := by
  constructor
  · exact NormalizerGraph.preservingGroup.mul_mem
      (NormalizerGraph.preservingGroup.mul_mem (transport_graph k) (hgraph g.val.property))
      (NormalizerGraph.preservingGroup.inv_mem (transport_graph k))
  · apply MulAction.mem_stabilizer_set.mpr
    intro x
    change transport k (representation g.val ((transport k)⁻¹ x)) ∈ Max3.sextet ↔
      x ∈ Max3.sextet
    rw [transport_mem]
    have hx : x ∈ Max3.sextet ↔ (transport k)⁻¹ x ∈ sextet k := by
      simpa using transport_mem k ((transport k)⁻¹ x)
    rw [hx]
    exact MulAction.mem_stabilizer_set.mp g.property _

/-- Both actual ambient sextet stabilizers satisfy the certified graph bound. -/
theorem sextetStabilizer_card_le
    (hgraph : permutationGroup ≤ NormalizerGraph.preservingGroup) (k : Fin 2) :
    Nat.card (sextetStabilizer k) ≤ 138240 := by
  have hc : Nat.card (sextetStabilizer k) ≤ Nat.card Max3.graphSextetGroup := by
    apply Nat.card_le_card_of_injective
      (fun g : sextetStabilizer k =>
        (⟨(MulAut.conj (transport k)) (representation g.val),
          transported_mem_graphSextetGroup hgraph k g⟩ : Max3.graphSextetGroup))
    intro g h he
    apply Subtype.ext
    apply representation_injective
    apply (MulAut.conj (transport k)).injective
    exact congrArg Subtype.val he
  exact hc.trans Max3.card_graphSextetGroup_le

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.RankSixCertificate
