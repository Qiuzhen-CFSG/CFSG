module
public import CFSG.Quasithin.Chapter10.SourceA5PointCarrierData

/-!
# Full movement of the original central-quotient image

The same elementary subgroup used in the carrier sieve is fully moved by the
literal image of L, and hence normalized by it. Together with the original
point Sylow normalization, this gives an invariant elementary subgroup for
the full local supplement. This is the input for minimal invariant subgroup
placement in the remaining sporadic point inspection.

Source: Aschbacher–Smith 10.2.9, printed pp.750–751.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- Full movement descends through the literal containing-center quotient. -/
theorem source_a5_containing_center_moved_commutator
    {I : Subgroup G} (hLI : L ≤ I) :
    let q := QuotientGroup.mk' (center I)
    let E := ((⁅D.fullModule,L⁆).subgroupOf I).map q
    let B := (L.subgroupOf I).map q
    ⁅E,B⁆ = E := by
  let W := ⁅D.fullModule,L⁆
  have hWI : W ≤ I := (source_full_moved_le_component D).trans hLI
  have hmove : ⁅W.subgroupOf I,L.subgroupOf I⁆ = W.subgroupOf I := by
    apply map_injective I.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWI,map_subgroupOf_eq_of_le hLI]
    exact source_full_moved_eq_commutator D
  exact (map_commutator _ _ (QuotientGroup.mk' (center I))).symm.trans
    (congrArg (map (QuotientGroup.mk' (center I))) hmove)

/-- The actual original local component normalizes the same moved image. -/
theorem source_a5_containing_center_moved_normalized
    {I : Subgroup G} (hLI : L ≤ I) :
    (L.subgroupOf I).map (QuotientGroup.mk' (center I)) ≤
      normalizer (((⁅D.fullModule,L⁆).subgroupOf I).map
        (QuotientGroup.mk' (center I)) : Set (I ⧸ center I)) := by
  have h := normalizer_commutator_ge_right
    (((⁅D.fullModule,L⁆).subgroupOf I).map (QuotientGroup.mk' (center I)))
    ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))
  rwa [source_a5_containing_center_moved_commutator D hLI] at h

/-- Both the actual component and full point Sylow preserve the original moved image. -/
theorem source_a5_point_supplement_normalizes_moved_image
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    {I : Subgroup G} (hLI : L ≤ I) (S : Sylow 2 I)
    (hSm : (S : Subgroup I).map I.subtype =
      ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) ⊓ I) :
    (L.subgroupOf I).map (QuotientGroup.mk' (center I)) ⊔
        (S.mapSurjective (QuotientGroup.mk'_surjective (center I)) : Subgroup (I ⧸ center I)) ≤
      normalizer (((⁅D.fullModule,L⁆).subgroupOf I).map
        (QuotientGroup.mk' (center I)) : Set (I ⧸ center I)) :=
  sup_le (source_a5_containing_center_moved_normalized D hLI)
    (source_a5_point_center_moved_normalized D hn hvL hv0 hLI S hSm)

end CFSG.Quasithin.Chapter10
