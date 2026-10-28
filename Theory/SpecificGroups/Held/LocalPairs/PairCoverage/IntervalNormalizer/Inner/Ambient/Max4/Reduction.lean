module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.Schreier
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer

/-!
# From finite max4 certificates to ambient containment

An element normalizing a literal entry preserves its actual orbit sizes. Its
Held permutation also preserves the published graph and is even. Thus checked
orbit labels and an even colored-graph bound bound the ambient normalizer.
A matching lower bound inside the literal local overgroup forces containment.

For four of the seven entries the fixed subgroup already supplies the needed
lower bound, using only the permitted representative orbit-cardinality input
and relative index two. The other three need additional local witnesses.
Neither the orbit tables, graph bounds, nor these witnesses are assumed to be
source theorems: they remain explicit finite inputs to this reduction.

Sources: GLS3 Table 5.3p and the literal ATLAS max4 calculation. This is a
cardinality argument on actual subgroups, without an abstract model catalogue
or any assumption about the full automorphism normalizer.
-/

public section
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4
open Subgroup
open Held.LocalPairs.SylowGeometry.Calculations (representative)

private def orbitMap (U : Subgroup He) (g : He)
    (hg : g ∈ normalizer (U : Set He)) (x : Fin 2058) :
    MulAction.orbit U x → MulAction.orbit U (g • x) := fun y =>
  ⟨g • y.val, by
    obtain ⟨p, hp⟩ := y.property
    change p.val • x = y.val at hp
    refine ⟨⟨g * p.val * g⁻¹, (mem_normalizer_iff.mp hg p.val).mp p.property⟩, ?_⟩
    change (g * p.val * g⁻¹) • (g • x) = g • y.val
    simpa only [mul_smul, inv_smul_smul] using congrArg (g • ·) hp⟩

private theorem orbit_card_invariant (U : Subgroup He) (g : He)
    (hg : g ∈ normalizer (U : Set He)) (x : Fin 2058) :
    Nat.card (MulAction.orbit U (g • x)) = Nat.card (MulAction.orbit U x) := by
  have hb (k : He) (hk : k ∈ normalizer (U : Set He)) (y : Fin 2058) :
      Nat.card (MulAction.orbit U y) ≤ Nat.card (MulAction.orbit U (k • y)) := by
    apply Nat.card_le_card_of_injective (orbitMap U k hk y)
    intro u v huv
    apply Subtype.ext
    exact (MulAction.injective k) (congrArg Subtype.val huv)
  exact le_antisymm (by simpa using hb g⁻¹ (inv_mem hg) (g • x)) (hb g hg x)

set_option maxRecDepth 4096 in
/-- Actual orbit cardinalities place the inner normalizer in the even colored
symmetries of the original Held graph. -/
theorem normalizer_mem_evenColoredGraphGroup (j : Fin 7)
    (horbits : ∀ x : Fin 2058,
      orbitSizeLabel j x = Nat.card (MulAction.orbit (candidate j) x))
    (g : He) (hg : g ∈ normalizer (candidate j : Set He)) :
    representation g ∈ evenColoredGraphGroup j := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup g.property
  · intro x
    rw [horbits, horbits]
    exact orbit_card_invariant (candidate j) g hg x
  · exact hom_to_commGroup_trivial (Equiv.Perm.sign.comp representation) g

/-- A certificate for the even colored-graph group bounds the ambient
normalizer, using the faithful representation. -/
theorem normalizer_card_le (j : Fin 7)
    (horbits : ∀ x : Fin 2058,
      orbitSizeLabel j x = Nat.card (MulAction.orbit (candidate j) x))
    (hgraph : Nat.card (evenColoredGraphGroup j) ≤ bound j) :
    Nat.card (normalizer (candidate j : Set He)) ≤ bound j := by
  apply (Nat.card_le_card_of_injective
    (fun g : normalizer (candidate j : Set He) =>
      (⟨representation g.val, normalizer_mem_evenColoredGraphGroup j horbits g.val g.property⟩ :
        evenColoredGraphGroup j)) ?_).trans hgraph
  intro g h he
  apply Subtype.ext
  apply representation_injective
  exact congrArg (fun z : evenColoredGraphGroup j => z.val) he

/-- Relative index two makes the fixed subgroup normalize the candidate. -/
theorem fixedSubgroup_le_normalizer (j : Fin 7)
    (hi : (candidate j).relIndex (fixedSubgroup true) = 2) :
    fixedSubgroup true ≤ normalizer (candidate j : Set He) :=
  (normal_subgroupOf_iff_le_normalizer
    (entry_le_fixedSubgroup true (pivot j) (mask j))).mp
    (normal_of_index_eq_two hi)

/-- Conjugation preserves the representative's cardinal lower bound. -/
theorem fixedSubgroup_card_ge
    (horbits : ∀ x : Fin 2058,
      SylowGeometry.Calculations.InnerNormalizer.orbitSizeLabel x =
        Nat.card (MulAction.orbit representative x)) :
    1024 ≤ Nat.card (fixedSubgroup true) := by
  have he := Nat.card_congr ((MulAut.conj (fixedConjugator true)).subgroupMap
    representative).toEquiv
  change Nat.card representative = Nat.card (fixedSubgroup true) at he
  rw [← he]
  exact SylowGeometry.Calculations.InnerNormalizer.representative_card_ge_of_orbit_labels horbits

/-- The fixed subgroup supplies a local lower bound for every index-two entry. -/
theorem local_normalizer_card_ge_1024
    (horbits : ∀ x : Fin 2058,
      SylowGeometry.Calculations.InnerNormalizer.orbitSizeLabel x =
        Nat.card (MulAction.orbit representative x))
    (j : Fin 7) (hi : (candidate j).relIndex (fixedSubgroup true) = 2) :
    1024 ≤ Nat.card ↥(normalizer (candidate j : Set He) ⊓ localOvergroup true) := by
  have hle : fixedSubgroup true ≤
      normalizer (candidate j : Set He) ⊓ localOvergroup true :=
    le_inf (fixedSubgroup_le_normalizer j hi) (fixedSubgroup_le_localOvergroup true)
  exact (fixedSubgroup_card_ge horbits).trans (Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle))

/-- Matching the upper bound within the actual local overgroup gives the
required inclusion in that overgroup. -/
theorem candidate_normalizer_le_of_bounds (j : Fin 7)
    (hupper : Nat.card (normalizer (candidate j : Set He)) ≤ bound j)
    (hlower : bound j ≤
      Nat.card ↥(normalizer (candidate j : Set He) ⊓ localOvergroup true)) :
    normalizer (candidate j : Set He) ≤ localOvergroup true := by
  have he := eq_of_le_of_card_ge (show
    normalizer (candidate j : Set He) ⊓ localOvergroup true ≤
      normalizer (candidate j : Set He) from inf_le_left) (hupper.trans hlower)
  exact (le_of_eq he.symm).trans inf_le_right

/-- Conditional assembly for all original pivots and masks. The finite
certificates in the first three hypotheses must still be supplied. The final
orbit-table premise is the representative premise allowed by the parent task. -/
theorem entry_normalizer_le_of_certificates
    (hentryOrbits : ∀ (j : Fin 7) (x : Fin 2058),
      orbitSizeLabel j x = Nat.card (MulAction.orbit (candidate j) x))
    (hgraph : ∀ j : Fin 7, Nat.card (evenColoredGraphGroup j) ≤ bound j)
    (hlarge : ∀ j : Fin 7, bound j = 3072 →
      (candidate j).relIndex (fixedSubgroup true) = 2 →
      3072 ≤ Nat.card ↥(normalizer (candidate j : Set He) ⊓ localOvergroup true))
    (horbits : ∀ x : Fin 2058,
      SylowGeometry.Calculations.InnerNormalizer.orbitSizeLabel x =
        Nat.card (MulAction.orbit representative x))
    (k : Fin 4) (m : Fin 4 → Bool) (hk : m k = true)
    (hc : localWord true ^ 5 ∈ entry true k m)
    (hi : (entry true k m).relIndex (fixedSubgroup true) = 2) :
    normalizer (entry true k m : Set He) ≤ localOvergroup true := by
  obtain ⟨j, hj⟩ := exists_candidate k m hk hi hc
  rw [← hj] at hi ⊢
  apply candidate_normalizer_le_of_bounds j (normalizer_card_le j (hentryOrbits j) (hgraph j))
  have hb : bound j = 1024 ∨ bound j = 3072 := by fin_cases j <;> decide
  rcases hb with hb | hb
  · rw [hb]
    exact local_normalizer_card_ge_1024 horbits j hi
  · rw [hb]
    exact hlarge j hb hi

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4
