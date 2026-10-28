module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SourceConfiguration
public import Theory.GroupTheory.SaturatedCentralProjection

/-!
# Literal component projections of the saturated local pair

The maximal pair constructed in the source yields saturation for subgroups
of the original H. Transporting that saturation along H's actual inclusion
allows the centralizer-quotient argument, retaining any central two-overlap.
An inner noncentral marked involution then gives a noncentral element of
the actual intersection with the pair core. Unique Sylow containment,
when supplied by the component's model geometry, identifies that intersection
with an actual Sylow subgroup of the component orbit.

Source: Aschbacher--Smith 2.5.3(3--4), printed pp.552--553. The center-two
and inner-action facts are earlier 2.5.2 conclusions; the three Bender
model calculations supply the separate Sylow-uniqueness condition.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

omit [Finite G] in
private theorem internal_saturation
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU) :
    ∀ P : Subgroup H, IsPGroup 2 P →
      HU.subgroupOf H ≤ normalizer (P : Set H) →
        P ≤ (twoCore HU).subgroupOf H := by
  intro P hp hn x hx
  have hna : HU ≤ normalizer (P.map H.subtype : Set G) := by
    intro a ha
    exact P.le_normalizer_map H.subtype
      ⟨⟨a, hpair.2 ha⟩, hn ha, rfl⟩
  exact hsat (P.map H.subtype) (map_subtype_le P) (hp.map H.subtype) hna
    (mem_map_of_mem H.subtype hx)

omit [Finite G] in
private theorem internal_core_normalization
    (_hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H) :
    HU.subgroupOf H ≤ normalizer ((twoCore HU).subgroupOf H : Set H) := by
  intro a ha x
  exact le_normalizer_twoCore HU ha (x : G)

omit [Finite G] in
/-- The actual quotient projection equals the literal core intersection,
including the genuine central two-cover case. -/
theorem saturated_pair_projection
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) [D.Normal] (hZ : IsPGroup 2 (center D)) :
    D ⊓ ((twoCore HU).subgroupOf H ⊔ centralizer (D : Set H)) =
      D ⊓ (twoCore HU).subgroupOf H :=
  inf_sup_centralizer_eq_inf_of_saturation D (HU.subgroupOf H)
    ((twoCore HU).subgroupOf H) hZ (isPGroup_pCoreIn 2 HU).comap_subtype
    (internal_core_normalization hpair) (internal_saturation hpair hsat)

omit [Finite G] in
/-- The original marked element gives a noncentral point of the original
component-orbit intersection, without a chosen splitting or projection map. -/
theorem saturated_pair_noncentral_projection
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) [D.Normal] (hZ : IsPGroup 2 (center D))
    (z : H) (hz : (z : G) ∈ twoCore HU)
    (hinner : z ∈ D ⊔ centralizer (D : Set H))
    (hnoncentral : z ∉ centralizer (D : Set H)) :
    ∃ d ∈ D ⊓ (twoCore HU).subgroupOf H, d ∉ centralizer (D : Set H) :=
  exists_noncentral_mem_inf_of_saturation D (HU.subgroupOf H)
    ((twoCore HU).subgroupOf H) hZ (isPGroup_pCoreIn 2 HU).comap_subtype
    (internal_core_normalization hpair) (internal_saturation hpair hsat)
    hz hinner hnoncentral

/-- Model Sylow uniqueness promotes the saturated core intersection to
a Sylow subgroup, with the exact original H and component-orbit inclusions. -/
theorem saturated_pair_sylow_intersection
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) [D.Normal]
    (hunique : ∀ P R : Sylow 2 D,
      ((twoCore HU).subgroupOf H).subgroupOf D ≤ P →
      ((twoCore HU).subgroupOf H).subgroupOf D ≤ R → P = R) :
    ∃ P : Sylow 2 D, ((P : Subgroup D).map D.subtype).map H.subtype =
      D.map H.subtype ⊓ twoCore HU := by
  obtain ⟨P, hP⟩ := exists_sylow_eq_inf_of_saturation D (HU.subgroupOf H)
    ((twoCore HU).subgroupOf H) (isPGroup_pCoreIn 2 HU).comap_subtype
    (internal_core_normalization hpair) (internal_saturation hpair hsat) hunique
  refine ⟨P, ?_⟩
  rw [hP]
  ext x
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨mem_map_of_mem H.subtype hd.1, hd.2⟩
  · rintro ⟨⟨d, hd, rfl⟩, hq⟩
    exact ⟨d, ⟨hd, hq⟩, rfl⟩

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
