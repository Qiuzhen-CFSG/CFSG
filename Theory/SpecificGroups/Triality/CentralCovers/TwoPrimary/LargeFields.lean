module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.RootRelations
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.HighestLong
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.RootPreimages
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Exchanges

/-!
# The large-field triality lifting assembly

For q ≥ 4, abelianness of the six individual root preimages constructs a
unique torus-normalized family of additive sections in the actual canonical
central cover. The triality exchange calculations hold for this same family
in the cover itself. Filtered collection therefore splits the literal positive
subgroup, and central transfer excludes two from the canonical kernel.

`RootPreimages` supplies abelianness and the normalized family; `Exchanges`
supplies its strict-height correction words in both exchange orders. The
unconditional results below discharge both inputs of the preserved conditional
assembly. They include the fixed field of order four: long-root preimages use
the highest-root argument and Weyl transport, and normalization uses a
cubic-field norm actor. No greater-than-four bound on the fixed field is used.

Sources: GLS3 §§2.4 and 6.1, Theorem 6.1.4 and Tables 6.1.2–3;
Aschbacher–Smith A.2.4 and I.1.3, PDF pp.44 and 418.
-/

public section
namespace Triality.Standard.CentralCovers.TwoPrimary
open PerfectCentralCovering

/-- Apply the normalization construction to the literal universal projection,
given the individual root-preimage calculation. -/
theorem universal_exists_torusNormalized_of_rootPreimagesAbelian
    (n : ℕ) (hn : 0 < n) (hlarge : 2 ≤ n)
    (hab : RootPreimagesAbelian n hn (universalProjection (BinaryCarrier n hn))) :
    ∃! L : RootSections n hn (universalProjection (BinaryCarrier n hn)),
      L.TorusNormalized :=
  existsUnique_torusNormalized_of_rootPreimagesAbelian n hn _ hlarge
    (universalProjection_surjective _) (universalProjection_ker_le_center _) hab

/-- The two independent local calculations supply one common compatible system.
The exchange input concerns the uniquely normalized sections. -/
theorem universal_higherCommutators_of_normalized_calculations
    (n : ℕ) (hn : 0 < n) (hlarge : 2 ≤ n)
    (hab : RootPreimagesAbelian n hn (universalProjection (BinaryCarrier n hn)))
    (hrelations : ∀ L : RootSections n hn (universalProjection (BinaryCarrier n hn)),
      L.TorusNormalized → L.HigherCommutators) :
    ∃ L : RootSections n hn (universalProjection (BinaryCarrier n hn)),
      L.HigherCommutators := by
  obtain ⟨L, hL, _⟩ :=
    universal_exists_torusNormalized_of_rootPreimagesAbelian n hn hlarge hab
  exact ⟨L, hrelations L hL⟩

/-- The literal canonical-kernel consumer of the two supplied calculations. -/
theorem universal_not_two_dvd_kernel_of_normalized_calculations
    (n : ℕ) (hn : 0 < n) (hlarge : 2 ≤ n)
    (hab : RootPreimagesAbelian n hn (universalProjection (BinaryCarrier n hn)))
    (hrelations : ∀ L : RootSections n hn (universalProjection (BinaryCarrier n hn)),
      L.TorusNormalized → L.HigherCommutators) :
    ¬ 2 ∣ Nat.card (universalProjection (BinaryCarrier n hn)).ker := by
  obtain ⟨L, hL⟩ :=
    universal_higherCommutators_of_normalized_calculations n hn hlarge hab hrelations
  exact universal_not_two_dvd_kernel_of_higherCommutators n hn L hL

/-- The canonical normalized family satisfies all exchanges in the covering
group, with every correction factor strictly above both exchanged heights. -/
theorem universalTorusNormalizedRootSections_higherCommutators
    (n : ℕ) (hn : 0 < n) (hlarge : 2 ≤ n) :
    (universalTorusNormalizedRootSections n hn hlarge).HigherCommutators :=
  universal_higherCommutators_of_torusNormalized n hn hlarge
    (universalTorusNormalizedRootSections n hn hlarge)
    (universalTorusNormalizedRootSections_torusNormalized n hn hlarge)

/-- One common compatible system of the six prescribed additive root lifts
exists for every q = 2^n ≥ 4, including q = 4. -/
theorem universal_exists_higherCommutators_of_two_le
    (n : ℕ) (hn : 0 < n) (hlarge : 2 ≤ n) :
    ∃ L : RootSections n hn (universalProjection (BinaryCarrier n hn)),
      L.HigherCommutators :=
  ⟨universalTorusNormalizedRootSections n hn hlarge,
    universalTorusNormalizedRootSections_higherCommutators n hn hlarge⟩

/-- Two does not divide the kernel of the literal universal projection of
the genuine binary triality carrier when q ≥ 4. This discharges the large-field
two-primary input; the odd-part calculation is independent. -/
theorem universal_not_two_dvd_kernel_of_two_le
    (n : ℕ) (hn : 0 < n) (hlarge : 2 ≤ n) :
    ¬ 2 ∣ Nat.card (universalProjection (BinaryCarrier n hn)).ker := by
  obtain ⟨L, hL⟩ := universal_exists_higherCommutators_of_two_le n hn hlarge
  exact universal_not_two_dvd_kernel_of_higherCommutators n hn L hL

end Triality.Standard.CentralCovers.TwoPrimary
