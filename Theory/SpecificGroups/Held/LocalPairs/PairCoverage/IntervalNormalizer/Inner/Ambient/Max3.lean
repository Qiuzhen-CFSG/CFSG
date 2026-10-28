module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Representatives
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.CoreWitness
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Reduction
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.OrbitData
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.OrbitCertificates
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.SextetStabilizer
public import Theory.SpecificGroups.Held.Model.Perfect
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.SeventeenSylow.Preservation

/-!
# The max3 interval normalizer calculation

The core-word identity and the relative-index-two condition reduce every
label and pivot to seven canonical entries. A normalizer transports actual
orbits bijectively, so their cardinalities give invariant colors. Every Held
permutation preserves the published graph and is even, by already proved
properties of the literal carrier.

The imported finite certificates identify the orbit-size tables, force the
even colored graph groups to preserve the six-point set, and identify its
actual Held stabilizer with max3. Their assembly handles every original mask
and pivot. Only the explicitly permitted representative orbit-size identity
remains for the parent ambient assembly to discharge.

Sources: GLS3 Table 5.3p; literal ATLAS HeG1-p2058B0/max3 programs. This is an
additional Held calculation, not the Lie-type argument on quasithin pp.747–748.
The orbit transport generalizes the existing representative InnerNormalizer
argument without importing the Ambient assembly root.
-/

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3
open Subgroup

private def orbitMap (U : Subgroup He) (g : He) (hg : g ∈ normalizer (U : Set He))
    (x : Fin 2058) : MulAction.orbit U x → MulAction.orbit U (g • x) := fun y =>
  ⟨g • y.val, by
    obtain ⟨p, hp⟩ := y.property
    change p.val • x = y.val at hp
    refine ⟨⟨g * p.val * g⁻¹, (mem_normalizer_iff.mp hg p.val).mp p.property⟩, ?_⟩
    change (g * p.val * g⁻¹) • (g • x) = g • y.val
    simpa only [mul_smul, inv_smul_smul] using congrArg (g • ·) hp⟩

private theorem orbit_card_normalizer_invariant (U : Subgroup He)
    (g : He) (hg : g ∈ normalizer (U : Set He)) (x : Fin 2058) :
    Nat.card (MulAction.orbit U (g • x)) = Nat.card (MulAction.orbit U x) := by
  have hb (k : He) (hk : k ∈ normalizer (U : Set He)) (y : Fin 2058) :
      Nat.card (MulAction.orbit U y) ≤ Nat.card (MulAction.orbit U (k • y)) := by
    apply Nat.card_le_card_of_injective (orbitMap U k hk y)
    intro u v huv
    apply Subtype.ext
    exact (MulAction.injective k) (congrArg Subtype.val huv)
  exact le_antisymm (by simpa using hb g⁻¹ (inv_mem hg) (g • x)) (hb g hg x)

set_option maxRecDepth 4096 in
/-- Correct orbit labels place the actual entry normalizer in the specified
even colored graph group. Graph preservation and parity are already proved. -/
public theorem normalizer_mem_evenColoredGraphGroup
    (t : Fin 7)
    (horbits : ∀ x : Fin 2058,
      orbitSizeLabel t x = Nat.card (MulAction.orbit (selectedEntry t) x))
    (g : He) (hg : g ∈ normalizer (selectedEntry t : Set He)) :
    representation g ∈ evenColoredGraphGroup t := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup g.property
  · intro x
    rw [horbits, horbits]
    exact orbit_card_normalizer_invariant (selectedEntry t) g hg x
  · exact hom_to_commGroup_trivial (Equiv.Perm.sign.comp representation) g

/-- A selected entry is handled by its orbit certificate, a graph inclusion,
and the independent geometric identification of the six-set stabilizer. -/
public theorem selected_normalizer_le_of_certificates
    (t : Fin 7)
    (horbits : ∀ x : Fin 2058,
      orbitSizeLabel t x = Nat.card (MulAction.orbit (selectedEntry t) x))
    (hcolors : evenColoredGraphGroup t ≤ sextetPermutationStabilizer)
    (hgeometry : sextetStabilizer ≤ localOvergroup false) :
    normalizer (selectedEntry t : Set He) ≤ localOvergroup false := by
  intro g hg
  apply hgeometry
  exact hcolors (normalizer_mem_evenColoredGraphGroup t horbits g hg)

/-- Conditional assembly for every original mask and every pivot. The three
finite certificates must all be discharged before the max3 target is complete. -/
public theorem normalizer_le_of_finite_certificates
    (horbits : ∀ (t : Fin 7) (x : Fin 2058),
      orbitSizeLabel t x = Nat.card (MulAction.orbit (selectedEntry t) x))
    (hcolors : ∀ t : Fin 7, evenColoredGraphGroup t ≤ sextetPermutationStabilizer)
    (hgeometry : sextetStabilizer ≤ localOvergroup false)
    (k : Fin 4) (mask : Fin 4 → Bool) (hk : mask k = true)
    (hw : localWord false ^ 6 ∈ entry false k mask)
    (hi : (entry false k mask).relIndex (fixedSubgroup false) = 2) :
    normalizer (entry false k mask : Set He) ≤ localOvergroup false := by
  obtain ⟨t, ht⟩ := exists_selected_entry k mask hk hw hi
  rw [ht]
  exact selected_normalizer_le_of_certificates t (horbits t) (hcolors t) hgeometry

/-- Every labelled max3 entry of relative index two containing the certified
core word has its ambient normalizer in the literal max3 local overgroup.
The entry orbit, colored-graph and sextet-stabilizer certificates are discharged;
only the permitted representative orbit identity remains for the ambient owner. -/
public theorem entry_normalizer_le
    (horbitsP : ∀ x : Fin 2058,
      SylowGeometry.Calculations.InnerNormalizer.orbitSizeLabel x =
        Nat.card (MulAction.orbit SylowGeometry.Calculations.representative x))
    (k : Fin 4) (mask : Fin 4 → Bool) (hk : mask k = true)
    (hw : localWord false ^ 6 ∈ entry false k mask)
    (hi : (entry false k mask).relIndex (fixedSubgroup false) = 2) :
    normalizer (entry false k mask : Set He) ≤ localOvergroup false :=
  normalizer_le_of_finite_certificates orbitSizeLabel_eq_card_orbit
    (evenColoredGraphGroup_le_sextet horbitsP)
    (sextetStabilizer_le_localOvergroup horbitsP) k mask hk hw hi

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3
