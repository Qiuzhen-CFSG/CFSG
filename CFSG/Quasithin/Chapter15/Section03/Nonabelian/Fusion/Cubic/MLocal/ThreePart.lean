module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry.Transport
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# The three-parts of the marked M-local centralizers

The literal orthogonal action has pointwise plane stabilizers of order six,
and the stabilizer of each nonidentity vector in a definite plane has order
twelve. Small finite certificates compute these two orders. Compatibility
identifies their inverse images with the actual centralizers in M.

The earlier source conclusion 15.3.49(4) says C_M(V) has order prime to three.
Its subgroups are therefore also prime to three, and the actor restricts
injectively to each local Sylow three-group. Surjective Sylow transport then
proves that every Sylow three-group of C_M(V₁), or of C_M(v) for nonidentity
v in V₁, has order three. No local Sylow witness is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the setup of
15.3.60 and proof of 15.3.61(1), printed p.1150; the orthogonal action is
15.3.2(1) and the definite-plane marking on pp.1121–1122.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal
open OrthogonalGeometry
local instance : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction

private instance : Fintype OrthogonalActor := Fintype.ofEquiv
  ((OrthogonalPlaneIndex → OrthogonalPlaneActor) × OrthogonalPlaneIndex)
  (RegularWreathProduct.equivProd _ _).symm

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 4000 in
private theorem finite_plane_count : ∀ i : OrthogonalPlaneIndex,
    Fintype.card {g : OrthogonalActor //
      ∀ w : OrthogonalVector, (∀ j, j ≠ i → w j = 1) → g • w = w} = 6 := by
  decide +kernel

set_option maxRecDepth 4000 in
private theorem finite_point_count : ∀ i : OrthogonalPlaneIndex, ∀ w : OrthogonalVector,
    (∀ j, j ≠ i → w j = 1) → w ≠ 1 →
      Fintype.card {g : OrthogonalActor // g • w = w} = 12 := by
  decide +kernel

set_option synthInstance.maxSize 10000 in
theorem card_pointwise_plane (i : OrthogonalPlaneIndex) :
    Nat.card (pointwise (orthogonalCoordinatePlane i)) = 6 := by
  change Nat.card {g : OrthogonalActor //
    ∀ w : OrthogonalVector, (∀ j, j ≠ i → w j = 1) → g • w = w} = 6
  rw [Nat.card_eq_fintype_card]
  exact finite_plane_count i

theorem card_stabilizer_plane_point (i : OrthogonalPlaneIndex) (w : OrthogonalVector)
    (hw : w ∈ orthogonalCoordinatePlane i) (hne : w ≠ 1) :
    Nat.card (MulAction.stabilizer OrthogonalActor w) = 12 := by
  change Nat.card {g : OrthogonalActor // g • w = w} = 12
  rw [Nat.card_eq_fintype_card]
  exact finite_point_count i w hw hne

theorem pointwise_zpowers (w : OrthogonalVector) :
    pointwise (zpowers w) = MulAction.stabilizer OrthogonalActor w := by
  ext g
  constructor
  · intro hg
    exact hg w (mem_zpowers w)
  · intro hg u hu
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hu
    change g • w = w at hg
    simp only [smul_zpow', hg]

variable {G : Type*} [Group G] {M V : Subgroup G}

/-- The actual conjugation actor restricted to the local vector centralizer. -/
def centralizerActor (d : NaturalOrthogonalAction M V) (A : Subgroup OrthogonalVector) :
    (M ⊓ centralizer (A.map d.vectorEmbedding : Set G) : Subgroup G) →* OrthogonalActor :=
  d.actor.comp (inclusion inf_le_left)

theorem range_centralizerActor (d : NaturalOrthogonalAction M V)
    (A : Subgroup OrthogonalVector) : (centralizerActor d A).range = pointwise A := by
  have he := d.centralizer_map_eq_comap A
  ext g
  constructor
  · rintro ⟨m, rfl⟩
    have h : (⟨m, m.property.1⟩ : M) ∈
        (centralizer (A.map d.vectorEmbedding : Set G)).subgroupOf M := m.property.2
    rw [he] at h
    exact h
  · intro hg
    obtain ⟨m, hm⟩ := d.onto g
    have h : m ∈ (centralizer (A.map d.vectorEmbedding : Set G)).subgroupOf M := by
      rw [he]
      change d.actor m ∈ pointwise A
      rwa [hm]
    exact ⟨⟨m, m.property, h⟩, hm⟩

theorem coprime_ker_centralizerActor [Finite G] (d : NaturalOrthogonalAction M V)
    (hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)))
    (A : Subgroup OrthogonalVector) : Nat.Coprime 3 (Nat.card (centralizerActor d A).ker) := by
  rw [← d.ker_actor] at hcop
  let f : (M ⊓ centralizer (A.map d.vectorEmbedding : Set G) : Subgroup G) →* M :=
    inclusion inf_le_left
  have hi : Function.Injective f := inclusion_injective _
  apply hcop.of_dvd_right
  rw [← card_map_of_injective hi]
  apply card_dvd_of_le
  rintro x ⟨m, hm, rfl⟩
  exact hm

private theorem sylow_card_via_range {H Q : Type*} [Group H] [Finite H] [Group Q]
    (f : H →* Q) (hcop : Nat.Coprime 3 (Nat.card f.ker)) (P : Sylow 3 H) :
    Nat.card P = 3 ^ (Nat.card f.range).factorization 3 := by
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let q := f.rangeRestrict
  have hq : Nat.Coprime 3 (Nat.card q.ker) := by
    simpa only [q, MonoidHom.ker_rangeRestrict] using hcop
  have hi := injective_comp_subtype_of_coprime_ker q hq (P : Subgroup H) P.isPGroup'
  have hc := Nat.card_congr (MonoidHom.ofInjective hi).toEquiv
  rw [MonoidHom.range_comp, range_subtype] at hc
  rw [hc]
  exact (P.mapSurjective f.rangeRestrict_surjective).card_eq_multiplicity

theorem sylow_card_vector_centralizer [Finite G] (d : NaturalOrthogonalAction M V)
    (hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)))
    (A : Subgroup OrthogonalVector)
    (P : Sylow 3 (M ⊓ centralizer (A.map d.vectorEmbedding : Set G) : Subgroup G)) :
    Nat.card P = 3 ^ (Nat.card (pointwise A)).factorization 3 := by
  have h := sylow_card_via_range (centralizerActor d A)
    (coprime_ker_centralizerActor d hcop A) P
  rwa [range_centralizerActor] at h

theorem sylow_three_card_plane [Finite G] (d : NaturalOrthogonalAction M V)
    (hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)))
    (i : OrthogonalPlaneIndex)
    (P : Sylow 3 (M ⊓ centralizer (d.plane i : Set G) : Subgroup G)) : Nat.card P = 3 := by
  have h : ∀ P : Sylow 3 (M ⊓ centralizer
      ((orthogonalCoordinatePlane i).map d.vectorEmbedding : Set G) : Subgroup G), Nat.card P = 3 := by
    intro P
    rw [sylow_card_vector_centralizer d hcop, card_pointwise_plane]
    decide +kernel
  rw [← d.plane_eq_map] at h
  exact h P

theorem sylow_three_card_plane_involution [Finite G] (d : NaturalOrthogonalAction M V)
    (hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)))
    (i : OrthogonalPlaneIndex) (v : G) (hv : v ∈ d.plane i) (hne : v ≠ 1)
    (P : Sylow 3 (M ⊓ centralizer ({v} : Set G) : Subgroup G)) : Nat.card P = 3 := by
  rw [d.plane_eq_map] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  have hwne : w ≠ 1 := by intro he; exact hne (by rw [he, map_one])
  have h : ∀ P : Sylow 3 (M ⊓ centralizer
      ((zpowers w).map d.vectorEmbedding : Set G) : Subgroup G), Nat.card P = 3 := by
    intro P
    rw [sylow_card_vector_centralizer d hcop, pointwise_zpowers,
      card_stabilizer_plane_point i w hw hwne]
    decide +kernel
  rw [MonoidHom.map_zpowers, zpowers_eq_closure, centralizer_closure] at h
  exact h P

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal
