module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.FullCentralizer

/-!
# Pointwise Sylow fixers in the Held automorphism group

The published nontrivial two-subgroup has a centralizer of order at most two
in the full permutation normalizer. Its nontrivial center embeds into that
centralizer and exhausts it, so every element of the centralizer belongs to
the embedded Held group. Sylow conjugacy puts a conjugate of the published
subgroup in any given Sylow two-subgroup.

Consequently an automorphism fixing a Sylow two-subgroup pointwise is inner,
provided every automorphism is realized by the full permutation normalizer.
Full realization remains the sole explicit producer premise. Nontriviality,
the two-group property and the full centralizer bound are all proved inputs;
no Sylow assertion about the published representative is required.

Sources: GLS3, Table 5.3p; the ATLAS HeG1-p2058B0 and HeG1-max3W1
representations underlying the imported finite certificates.
-/

public section

open Subgroup
open scoped Pointwise

namespace Held.LocalPairs.SylowPointwise

open SylowGeometry SylowGeometry.Calculations

/-- The centralizer of the published representative in the full permutation
normalizer consists of embedded Held elements. -/
theorem representative_fullCentralizer_le_inner :
    centralizer (representative.map innerEmbedding : Set PermutationNormalizer) ≤
      innerEmbedding.range := by
  let f : representative →* PermutationNormalizer :=
    innerEmbedding.comp representative.subtype
  let Z : Subgroup PermutationNormalizer := (center representative).map f
  have hf : Function.Injective f :=
    innerEmbedding_injective.comp representative.subtype_injective
  have hZC : Z ≤ centralizer
      (representative.map innerEmbedding : Set PermutationNormalizer) := by
    rintro _ ⟨z, hz, rfl⟩
    apply mem_centralizer_iff.mpr
    rintro _ ⟨b, hb, rfl⟩
    exact (map_mul f _ _).symm.trans
      ((congrArg f ((mem_center_iff.mp hz) ⟨b, hb⟩)).trans (map_mul f _ _))
  let : Nontrivial representative :=
    (Subgroup.nontrivial_iff_ne_bot representative).mpr representative_ne_bot
  let : Nontrivial (center representative) := representative_isPGroup.center_nontrivial
  have hZcard : 2 ≤ Nat.card Z := by
    rw [Subgroup.card_map_of_injective hf]
    exact Finite.one_lt_card
  have heq : Z = centralizer
      (representative.map innerEmbedding : Set PermutationNormalizer) :=
    eq_of_le_of_card_ge hZC (representative_fullCentralizer_card_le_two.trans hZcard)
  rw [← heq]
  rintro _ ⟨z, _, rfl⟩
  exact ⟨z, rfl⟩

private theorem isInner_of_fixes_representative
    (hrealize : Function.Surjective permutationGroup.normalizerMonoidHom)
    (a : MulAut He) (hfix : ∀ x ∈ representative, a x = x) :
    ∃ g : He, MulAut.conj g = a := by
  obtain ⟨n, rfl⟩ := hrealize a
  have hn : n ∈ centralizer
      (representative.map innerEmbedding : Set PermutationNormalizer) := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨b, hb, rfl⟩
    apply Subtype.ext
    have hbfix := congrArg Subtype.val (hfix b hb)
    change n.val * b.val * n.val⁻¹ = b.val at hbfix
    change b.val * n.val = n.val * b.val
    exact (mul_inv_eq_iff_eq_mul.mp hbfix).symm
  obtain ⟨g, hg⟩ := representative_fullCentralizer_le_inner hn
  exact ⟨g, (normalizerAction_innerEmbedding g).symm.trans
    (congrArg permutationGroup.normalizerMonoidHom hg)⟩

/-- Conditional on full realization, every automorphism fixing a Held Sylow
two-subgroup pointwise is inner. All representative calculations are discharged. -/
theorem isInner_of_fixes_sylow
    (hrealize : Function.Surjective permutationGroup.normalizerMonoidHom)
    (S : Sylow 2 He) (a : MulAut He)
    (hfix : ∀ x ∈ (S : Subgroup He), a x = x) :
    ∃ g : He, MulAut.conj g = a := by
  obtain ⟨P, hBP⟩ := representative_isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq He P S
  let c : MulAut He := MulAut.conj g
  let b : MulAut He := c⁻¹ * a * c
  have hbfix : ∀ x ∈ representative, b x = x := by
    intro x hx
    have hxS : c x ∈ (S : Subgroup He) := by
      rw [← hg]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hBP hx)
    change c.symm (a (c x)) = x
    rw [hfix _ hxS, c.symm_apply_apply]
  obtain ⟨k, hk⟩ := isInner_of_fixes_representative hrealize b hbfix
  refine ⟨g * k * g⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv]
  change c * MulAut.conj k * c⁻¹ = a
  rw [hk]
  change c * (c⁻¹ * a * c) * c⁻¹ = a
  group

end Held.LocalPairs.SylowPointwise
