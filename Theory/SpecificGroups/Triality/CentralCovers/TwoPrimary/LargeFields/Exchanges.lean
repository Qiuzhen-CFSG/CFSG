module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Normalization
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Exchanges.LongRoots
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Exchanges.Commuting
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Exchanges.ShortRoots

/-!
# Assembly of normalized triality exchanges

For q ≥ 4, torus normalization of the six supplied additive root sections
implies every exchange in the central extension. `Commuting` proves the ten
noninteracting pairs, `ShortRoots` proves the four polynomial short-root
exchanges using those commuting pairs, and `LongRoots` proves the remaining
A₂ exchange. Scalar-equivariant uniqueness removes their central defects.
The long-root argument uses a cubic-field unit with nonidentity norm, so the
field of order four is included without requiring a nonidentity cube in its
fixed field.

The collector gives correction factors strictly above both exchanged heights,
including reversed exchanges, and constructs a section of the literal positive
subgroup. Transfer then excludes two from the canonical kernel. The existence
of the supplied normalized root sections remains a separate input; no commuting
or polynomial exchange premise remains in the completed assembly below.

Sources: GLS3 §§2.4 and 6.1, Theorem 6.1.4 and Tables 6.1.2–3;
Aschbacher–Smith A.2.4 and I.1.3 (PDF pp.44 and 418).
-/

public section
namespace Triality.Standard.CentralCovers.TwoPrimary
open Parabolics PerfectCentralCovering
variable {n : ℕ} {hn : 0 < n} {E : Type*} [Group E]
variable {f : E →* BinaryCarrier n hn}

/-- Discharge the long-root exchange before applying the full collector.
The two remaining families concern exact equations in the extension. -/
theorem RootSections.higherCommutators_of_normalized_short_relations
    (L : RootSections n hn f) (hL : L.TorusNormalized) (hlarge : 2 ≤ n)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hC : L.CommutingRelations) (hS : L.ShortExchangeRelations) :
    L.HigherCommutators :=
  L.higherCommutators_of_relations hC hS (L.normalized_long_exchange hL hlarge hf hk)

/-- The literal positive-subgroup section, with its original projection map. -/
theorem RootSections.exists_unipotent_section_of_normalized_short_relations
    (L : RootSections n hn f) (hL : L.TorusNormalized) (hlarge : 2 ≤ n)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hC : L.CommutingRelations) (hS : L.ShortExchangeRelations) :
    ∃ s : unipotent (binaryParameters n hn) →* E,
      f.comp s = (unipotent (binaryParameters n hn)).subtype :=
  L.exists_unipotent_section
    (L.higherCommutators_of_normalized_short_relations hL hlarge hf hk hC hS)

/-- Canonical-kernel application of the completed long-root calculation.
The commuting and short-exchange families still have to be supplied. -/
theorem universal_not_two_dvd_kernel_of_normalized_short_relations
    (n : ℕ) (hn : 0 < n) (hlarge : 2 ≤ n)
    (L : RootSections n hn (universalProjection (BinaryCarrier n hn)))
    (hL : L.TorusNormalized) (hC : L.CommutingRelations) (hS : L.ShortExchangeRelations) :
    ¬ 2 ∣ Nat.card (universalProjection (BinaryCarrier n hn)).ker :=
  universal_not_two_dvd_kernel_of_higherCommutators n hn L
    (L.higherCommutators_of_normalized_short_relations hL hlarge
      (universalProjection_surjective _) (universalProjection_ker_le_center _) hC hS)

/-- Torus normalization implies every strict-height exchange in a surjective
central extension. All ten commuting pairs and all five interacting pairs
are proved, and the collector supplies both orders. -/
theorem RootSections.higherCommutators_of_torusNormalized
    (L : RootSections n hn f) (hL : L.TorusNormalized) (hlarge : 2 ≤ n)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    L.HigherCommutators := by
  have hC := L.normalized_commuting_relations hL hlarge hf hk
  exact L.higherCommutators_of_normalized_short_relations hL hlarge hf hk hC
    (L.normalized_short_exchanges hL hlarge hf hk hC)

/-- The literal positive-subgroup inclusion splits from the supplied normalized
sections, with every inter-root compatibility premise discharged. -/
theorem RootSections.exists_unipotent_section_of_torusNormalized
    (L : RootSections n hn f) (hL : L.TorusNormalized) (hlarge : 2 ≤ n)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    ∃ s : unipotent (binaryParameters n hn) →* E,
      f.comp s = (unipotent (binaryParameters n hn)).subtype :=
  L.exists_unipotent_section (L.higherCommutators_of_torusNormalized hL hlarge hf hk)

/-- The normalized-exchange input to the large-field canonical-cover assembly,
including n = 2. Only the supplied sections and their normalization are needed. -/
theorem universal_higherCommutators_of_torusNormalized
    (n : ℕ) (hn : 0 < n) (hlarge : 2 ≤ n)
    (L : RootSections n hn (universalProjection (BinaryCarrier n hn))) :
    L.TorusNormalized → L.HigherCommutators := fun hL =>
  L.higherCommutators_of_torusNormalized hL hlarge
    (universalProjection_surjective _) (universalProjection_ker_le_center _)

/-- Canonical-kernel exclusion from the supplied normalized sections. This
discharges the exchange calculation in the two-primary multiplier argument. -/
theorem universal_not_two_dvd_kernel_of_torusNormalized
    (n : ℕ) (hn : 0 < n) (hlarge : 2 ≤ n)
    (L : RootSections n hn (universalProjection (BinaryCarrier n hn)))
    (hL : L.TorusNormalized) :
    ¬ 2 ∣ Nat.card (universalProjection (BinaryCarrier n hn)).ker :=
  universal_not_two_dvd_kernel_of_higherCommutators n hn L
    (universal_higherCommutators_of_torusNormalized n hn hlarge L hL)

end Triality.Standard.CentralCovers.TwoPrimary
