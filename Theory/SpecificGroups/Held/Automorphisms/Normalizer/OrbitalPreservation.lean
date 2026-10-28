module

public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.OrbitalPreservation.OrbitUniqueness
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.OrbitalPreservation.GeneratorInvariance

/-!
# The full Held normalizer preserves the orbital relation

The point stabilizer has a unique invariant 425-element subset, namely row
zero of the published relation. The checked generator certificates prove that
Held preserves the relation. Conjugation by a normalizer element fixing zero
therefore preserves this characterization. Transitivity then transports the
result to every row.

The conditional transport theorem is retained, and `normalizer_le_preservingGroup`
discharges its invariance premise using the two original Held generators.
No simplicity, perfectness, exact group order, or graph-group cardinal bound
is used.

Source: GLS3 Table 5.3p and the fixed ATLAS degree-2058 representation.
-/

namespace Held.NormalizerGraph.Orbital

/-- The unique 425-point invariant set is fixed by every normalizer element
fixing zero, provided Held preserves the published relation. -/
private theorem normalizer_zero_of_invariant
    (hH : permutationGroup ≤ preservingGroup)
    (n : Equiv.Perm (Fin 2058))
    (hn : n ∈ Subgroup.normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058))))
    (hn0 : n 0 = 0) : ∀ y, Adj 0 (n y) ↔ Adj 0 y := by
  apply unique_invariant (fun y => Adj 0 (n y))
  · intro g x
    have hng : n * g.val.val * n⁻¹ ∈ preservingGroup :=
      hH ((Subgroup.mem_normalizer_iff.mp hn g.val.val).mp g.val.property)
    have hi0 : n.symm 0 = 0 := by
      apply n.injective
      rw [Equiv.apply_symm_apply, hn0]
    have hg0 : g.val.val 0 = 0 := g.property
    have he0 : (n * g.val.val * n⁻¹) 0 = 0 := by
      change n (g.val.val (n.symm 0)) = 0
      rw [hi0, hg0, hn0]
    have hex : (n * g.val.val * n⁻¹) (n x) = n (g • x) := by
      change n (g.val.val (n.symm (n x))) = n (g • x)
      rw [Equiv.symm_apply_apply]
      rfl
    simpa only [he0, hex] using hng 0 (n x)
  · exact (Nat.card_congr (Equiv.subtypeEquivOfSubtype n)).trans row_card

/-- Transitivity transports the distinguished invariant set to every row. -/
public theorem normalizer_le_of_invariant (hH : permutationGroup ≤ preservingGroup) :
    Subgroup.normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058))) ≤
      preservingGroup := by
  intro n hn x y
  obtain ⟨h, hh⟩ := Transitivity.exists_move_zero x
  obtain ⟨k, hk⟩ := Transitivity.exists_move_zero (n x)
  let m := (representation k)⁻¹ * n * representation h
  have hm : m ∈ Subgroup.normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058))) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.inv_mem _ (permutationGroup.le_normalizer k.property)) hn)
      (permutationGroup.le_normalizer h.property)
  have hm0 : m 0 = 0 := by
    change (representation k).symm (n (representation h 0)) = 0
    rw [hh, ← hk, Equiv.symm_apply_apply]
  have he := normalizer_zero_of_invariant hH m hm hm0 ((representation h).symm y)
  have hha : ∀ u v, Adj (representation h u) (representation h v) ↔ Adj u v := hH h.property
  have hka : ∀ u v, Adj (representation k u) (representation k v) ↔ Adj u v := hH k.property
  calc
    Adj (n x) (n y) ↔ Adj 0 ((representation k).symm (n y)) := by
      simpa only [hk, Equiv.apply_symm_apply] using
        hka 0 ((representation k).symm (n y))
    _ ↔ Adj 0 ((representation h).symm y) := by
      simpa only [m, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
        Equiv.apply_symm_apply] using he
    _ ↔ Adj x y := by
      simpa only [hh, Equiv.apply_symm_apply] using
        (hha 0 ((representation h).symm y)).symm
/-- The full permutation normalizer of the concrete Held group preserves the
published orbital relation, with no additional premises. -/
public theorem normalizer_le_preservingGroup :
    Subgroup.normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058))) ≤
      preservingGroup :=
  normalizer_le_of_invariant held_le_preservingGroup

end Held.NormalizerGraph.Orbital
