module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.Representative
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.FullCentralizer.Constraints
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.OrbitalPreservation
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.SeventeenSylow.Preservation

/-!
# The representative's centralizer in the full Held normalizer

The full permutation normalizer preserves the published Held orbital graph:
combine the existing orbital-uniqueness reduction with the independently
checked preservation by Held. A centralizer element commutes with each of
the four actual representative generators. The finite graph certificate
then makes evaluation at point zero injective, with at most two images.

This proves the full centralizer bound directly. No exhibited extension is
identified with the full normalizer, and no center cardinality, self-normalizer,
two-group, simplicity, perfectness or quotient-bound hypothesis is needed.
Source: GLS3 Table 5.3p; ATLAS HeG1-p2058B0 and HeG1-max3W1.
-/

namespace Held.LocalPairs.SylowGeometry.Calculations
open Held.NormalizerGraph
open FullCentralizer

private abbrev Centralizer := Subgroup.centralizer
  (representative.map innerEmbedding : Set PermutationNormalizer)

private lemma centralizer_commutes (c : Centralizer) : CommutesGenerators c.val.val := by
  intro i x
  have h := (Subgroup.mem_centralizer_iff.mp c.property) (innerEmbedding (generator i))
    (Subgroup.mem_map_of_mem innerEmbedding (generator_mem i))
  exact (congrArg (fun g : PermutationNormalizer => g.val x) h).symm

private lemma centralizer_preserves (c : Centralizer) : c.val.val ∈ preservingGroup :=
  Orbital.normalizer_le_of_invariant
    Held.Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup c.val.property

private lemma eval_zero_injective : Function.Injective (fun c : Centralizer => c.val.val (0 : Fin 2058)) := by
  intro c d h
  change c.val.val 0 = d.val.val 0 at h
  have hq : (d⁻¹ * c : Centralizer) = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    apply fix_zero_eq_one _ (centralizer_commutes _) (centralizer_preserves _)
    change d.val.val.symm (c.val.val 0) = 0
    rw [h, Equiv.symm_apply_apply]
  exact (inv_mul_eq_one.mp hq).symm

/-- The actual embedded representative has a centralizer of order at most two
in the full permutation normalizer. All finite and containment inputs are proved. -/
public theorem representative_fullCentralizer_card_le_two :
    Nat.card (Subgroup.centralizer
      (representative.map innerEmbedding : Set PermutationNormalizer)) ≤ 2 := by
  let f : Centralizer → {x : Fin 2058 // x = 0 ∨ x = 1395} := fun c =>
    ⟨c.val.val 0, images_zero _ (centralizer_commutes c)⟩
  have hf : Function.Injective f := by
    intro c d h
    exact eval_zero_injective (congrArg Subtype.val h)
  have hc : Nat.card {x : Fin 2058 // x = 0 ∨ x = 1395} = 2 := by
    rw [Nat.card_eq_fintype_card]
    set_option maxRecDepth 16384 in
      decide +kernel
  exact (Nat.card_le_card_of_injective f hf).trans hc.le

end Held.LocalPairs.SylowGeometry.Calculations
