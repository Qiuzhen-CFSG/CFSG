module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action
public import Stellmacher.OmegaOneCenterMap

/-!
# Transport of the orthogonal Sylow geometry

The coordinate embedding intertwines the literal wreath action with conjugation
in the ambient group. Fixed subgroups, plane normalizers and fixed-line
centralizers consequently transport through this embedding, with exact
cardinality and relative-index formulas. The actual Sylow subgroup has a Sylow
image under the surjective actor map. Independently of a fixed-space count,
the source definition `V = ⟨Ω₁(Z(T))^M⟩` gives `Ω₁(Z(T)) = C_V(T)`.

The final two local-index lemmas are conditional reductions: an index-two
plane stabilizer and an even actor-stabilizer index suffice because the Sylow
index in `M` is odd. They do not assume either desired local Sylow conclusion.
The concrete wreath calculations are separate prerequisites for the assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.2(2)
and the geometry preceding 15.3.5–6, printed pp.1121–1122.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03
open Subgroup

namespace OrthogonalGeometry
local instance : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction

/-- Fixed vectors for the specified literal wreath action. -/
def fixedVectors (H : Subgroup OrthogonalActor) : Subgroup OrthogonalVector where
  carrier w := ∀ g ∈ H, g • w = w
  one_mem' := by intro g hg; exact smul_one g
  mul_mem' := by intro a b ha hb g hg; rw [smul_mul', ha g hg, hb g hg]
  inv_mem' := by intro a ha g hg; rw [smul_inv', ha g hg]

/-- Setwise stabilizer of a vector subgroup in the specified action. -/
def setwise (A : Subgroup OrthogonalVector) : Subgroup OrthogonalActor where
  carrier g := ∀ w, g • w ∈ A ↔ w ∈ A
  one_mem' := by intro w; rw [one_smul]
  mul_mem' := by intro a b ha hb w; rw [mul_smul, ha, hb]
  inv_mem' := by
    intro a ha w
    simpa only [smul_inv_smul] using (ha (a⁻¹ • w)).symm

/-- Pointwise stabilizer, used for the local fixed-line centralizer. -/
def pointwise (A : Subgroup OrthogonalVector) : Subgroup OrthogonalActor where
  carrier g := ∀ w ∈ A, g • w = w
  one_mem' := by intro w hw; exact one_smul _ w
  mul_mem' := by intro a b ha hb w hw; rw [mul_smul, hb w hw, ha w hw]
  inv_mem' := by
    intro a ha w hw
    exact (inv_smul_eq_iff).mpr (ha w hw).symm
end OrthogonalGeometry

variable {G : Type*} [Group G]
namespace NaturalOrthogonalAction
variable {M V : Subgroup G} (d : NaturalOrthogonalAction M V)
local instance : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction
open OrthogonalGeometry

/-- The coordinate vectors embedded in the actual ambient group. -/
def vectorEmbedding : OrthogonalVector →* G := V.subtype.comp (d.coordinates.symm : OrthogonalVector →* V)

theorem vectorEmbedding_injective : Function.Injective d.vectorEmbedding :=
  V.subtype_injective.comp d.coordinates.symm.injective

theorem vectorEmbedding_conjugate (m : M) (w : OrthogonalVector) :
    d.vectorEmbedding (d.actor m • w) = (m : G) * d.vectorEmbedding w * (m : G)⁻¹ := by
  have h := d.compatible m (d.coordinates.symm w)
  rw [d.coordinates.apply_symm_apply] at h
  have he := congrArg (fun v => (d.coordinates.symm v : G)) h
  rw [d.coordinates.symm_apply_apply] at he
  exact he.symm

theorem vectorEmbedding_range : d.vectorEmbedding.range = V := by
  rw [vectorEmbedding, MonoidHom.range_comp, d.coordinates.symm.range_eq_top,
    ← MonoidHom.range_eq_map, range_subtype]

theorem plane_eq_map (i : OrthogonalPlaneIndex) :
    d.plane i = (orthogonalCoordinatePlane i).map d.vectorEmbedding := by
  rw [plane, vectorEmbedding, ← map_map,
    map_equiv_eq_comap_symm d.coordinates.symm]
  rfl

/-- The action image of the specified ambient Sylow subgroup is Sylow. -/
noncomputable def sylowImage [Finite G] (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) :
    Sylow 2 OrthogonalActor := (T.subtype hTM).mapSurjective d.onto

@[simp] theorem coe_sylowImage [Finite G] (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) : (d.sylowImage T hTM : Subgroup OrthogonalActor) =
      d.image T := rfl

/-- The coordinate fixed subgroup transports to the actual centralizer. -/
theorem fixedPlane_eq_map {X : Subgroup G} (hXM : X ≤ M) :
    fixedPlane V X = (fixedVectors (d.image X)).map d.vectorEmbedding := by
  ext x
  constructor
  · rintro ⟨hxV, hxC⟩
    refine ⟨d.coordinates ⟨x, hxV⟩, ?_, by simp [vectorEmbedding]⟩
    rintro a ⟨m, hm, rfl⟩
    apply d.vectorEmbedding_injective
    rw [d.vectorEmbedding_conjugate]
    have he : d.vectorEmbedding (d.coordinates ⟨x, hxV⟩) = x := by simp [vectorEmbedding]
    rw [he]
    exact mul_inv_eq_iff_eq_mul.mpr (hxC m hm)
  · rintro ⟨w, hw, rfl⟩
    refine ⟨(d.coordinates.symm w).property, ?_⟩
    intro t ht
    have he := congrArg d.vectorEmbedding (hw (d.actor ⟨t, hXM ht⟩) ⟨⟨t, hXM ht⟩, ht, rfl⟩)
    rw [d.vectorEmbedding_conjugate] at he
    exact mul_inv_eq_iff_eq_mul.mp he

/-- Cardinalities can be computed entirely in the literal vector model. -/
theorem card_fixedPlane {X : Subgroup G} (hXM : X ≤ M) :
    Nat.card (fixedPlane V X) = Nat.card (fixedVectors (d.image X)) := by
  rw [d.fixedPlane_eq_map hXM, card_map_of_injective d.vectorEmbedding_injective]

/-- Normalizers of vector subgroups are the preimages of their actual setwise stabilizers. -/
theorem normalizer_map_eq_comap (A : Subgroup OrthogonalVector) :
    (normalizer (A.map d.vectorEmbedding : Set G)).subgroupOf M =
      (setwise A).comap d.actor := by
  ext m
  change (m : G) ∈ normalizer (A.map d.vectorEmbedding : Set G) ↔ _
  rw [mem_normalizer_iff]
  constructor
  · intro hm w
    change d.actor m • w ∈ A ↔ w ∈ A
    rw [← mem_map_iff_mem d.vectorEmbedding_injective,
      d.vectorEmbedding_conjugate,
      ← hm (d.vectorEmbedding w), mem_map_iff_mem d.vectorEmbedding_injective]
  · intro hm x
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [← d.vectorEmbedding_conjugate]
      exact mem_map_of_mem _ ((hm w).mpr hw)
    · intro hx
      have hxV : x ∈ V := (mem_normalizer_iff.mp (d.normalizes m.property) x).mpr
        (d.vectorEmbedding_range ▸ (map_le_range d.vectorEmbedding A hx))
      let w := d.coordinates ⟨x, hxV⟩
      have he : d.vectorEmbedding w = x := by simp [w, vectorEmbedding]
      rw [← he, ← d.vectorEmbedding_conjugate,
        mem_map_iff_mem d.vectorEmbedding_injective] at hx
      rw [← he]
      exact mem_map_of_mem _ ((hm w).mp hx)

/-- Centralizers of vector subgroups are the preimages of their pointwise stabilizers. -/
theorem centralizer_map_eq_comap (A : Subgroup OrthogonalVector) :
    (centralizer (A.map d.vectorEmbedding : Set G)).subgroupOf M =
      (pointwise A).comap d.actor := by
  ext m
  constructor
  · intro hm w hw
    apply d.vectorEmbedding_injective
    rw [d.vectorEmbedding_conjugate]
    exact mul_inv_eq_iff_eq_mul.mpr (hm _ (mem_map_of_mem _ hw)).symm
  · intro hm
    rintro x ⟨w, hw, rfl⟩
    have he := congrArg d.vectorEmbedding (hm w hw)
    rw [d.vectorEmbedding_conjugate] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The plane normalizer restricts to precisely its coordinate stabilizer. -/
theorem plane_normalizer_eq_comap (i : OrthogonalPlaneIndex) :
    (normalizer (d.plane i : Set G)).subgroupOf M =
      (setwise (orthogonalCoordinatePlane i)).comap d.actor := by
  rw [d.plane_eq_map]
  exact d.normalizer_map_eq_comap _

/-- The stabilizer image is the intersection with the coordinate stabilizer. -/
theorem image_planeStabilizer (T : Sylow 2 G)
    (i : OrthogonalPlaneIndex) :
    d.image (planeStabilizer T (d.plane i)) =
      d.image T ⊓ setwise (orthogonalCoordinatePlane i) := by
  have he := d.plane_normalizer_eq_comap i
  ext g
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, hm.1, rfl⟩, (show m ∈ (setwise (orthogonalCoordinatePlane i)).comap d.actor
      from he ▸ hm.2)⟩
  · rintro ⟨⟨m, hm, rfl⟩, hg⟩
    refine ⟨m, ⟨hm, ?_⟩, rfl⟩
    exact (show m ∈ (normalizer (d.plane i : Set G)).subgroupOf M from he ▸ hg)

/-- Relative index of the ambient plane stabilizer is exactly the coordinate index. -/
theorem index_planeStabilizer (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (i : OrthogonalPlaneIndex) :
    ((planeStabilizer T (d.plane i)).subgroupOf T).index =
      (setwise (orthogonalCoordinatePlane i)).relIndex (d.image T) := by
  change (planeStabilizer T (d.plane i)).relIndex T = _
  rw [planeStabilizer, inf_relIndex_left,
    ← relIndex_subgroupOf hTM, d.plane_normalizer_eq_comap,
    relIndex_comap]
  rfl

/-- Coordinates for the fixed subgroup in one definite plane. -/
theorem plane_fixed_eq_map {X : Subgroup G} (hXM : X ≤ M) (i : OrthogonalPlaneIndex) :
    fixedPlane (d.plane i) X =
      (orthogonalCoordinatePlane i ⊓ fixedVectors (d.image X)).map d.vectorEmbedding := by
  rw [map_inf _ _ _ d.vectorEmbedding_injective, ← d.plane_eq_map,
    ← d.fixedPlane_eq_map hXM]
  change d.plane i ⊓ centralizer (X : Set G) =
    d.plane i ⊓ (V ⊓ centralizer (X : Set G))
  rw [← inf_assoc, inf_eq_left.mpr (d.plane_le i)]

theorem card_plane_fixed {X : Subgroup G} (hXM : X ≤ M) (i : OrthogonalPlaneIndex) :
    Nat.card (fixedPlane (d.plane i) X) =
      Nat.card ↥(orthogonalCoordinatePlane i ⊓ fixedVectors (d.image X)) := by
  rw [d.plane_fixed_eq_map hXM, card_map_of_injective d.vectorEmbedding_injective]

/-- The source local normalizer has the same index as the coordinate stabilizer. -/
theorem plane_normalizer_relIndex (i : OrthogonalPlaneIndex) :
    (M ⊓ normalizer (d.plane i : Set G)).relIndex M =
      (setwise (orthogonalCoordinatePlane i)).index := by
  rw [inf_relIndex_left]
  change ((normalizer (d.plane i : Set G)).subgroupOf M).index = _
  rw [d.plane_normalizer_eq_comap, index_comap_of_surjective _ d.onto]

/-- The source local centralizer has the index of the literal pointwise stabilizer. -/
theorem vector_centralizer_relIndex (A : Subgroup OrthogonalVector) :
    (M ⊓ centralizer (A.map d.vectorEmbedding : Set G)).relIndex M =
      (pointwise A).index := by
  rw [inf_relIndex_left]
  change ((centralizer (A.map d.vectorEmbedding : Set G)).subgroupOf M).index = _
  rw [d.centralizer_map_eq_comap, index_comap_of_surjective _ d.onto]

private theorem odd_local_index [Finite G] (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) {S K : Subgroup G}
    (hST : S ≤ T) (hSK : S ≤ K) (hKM : K ≤ M)
    (hS : S.relIndex T = 2) (hK : 2 ∣ K.relIndex M) : ¬ 2 ∣ S.relIndex K := by
  have hodd : ¬ 2 ∣ (T : Subgroup G).relIndex M := (T.subtype hTM).not_dvd_index
  have he := S.relIndex_mul_relIndex K M hSK hKM
  have heT := S.relIndex_mul_relIndex T M hST hTM
  rw [hS] at heT
  obtain ⟨k, hk⟩ := hK
  rw [hk, ← heT] at he
  have he' : S.relIndex K * k = (T : Subgroup G).relIndex M := by
    nlinarith [he]
  intro hn
  exact hodd (he' ▸ dvd_mul_of_dvd_left hn k)

/-- The even index of the coordinate plane stabilizer gives its local Sylow property. -/
theorem planeStabilizer_local_normalizer_index [Finite G]
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) (i : OrthogonalPlaneIndex)
    (hS : (setwise (orthogonalCoordinatePlane i)).relIndex (d.image T) = 2)
    (hN : 2 ∣ (setwise (orthogonalCoordinatePlane i)).index) :
    ¬ 2 ∣ (planeStabilizer T (d.plane i)).relIndex
      (M ⊓ normalizer (d.plane i : Set G)) := by
  apply odd_local_index T hTM inf_le_left
    (le_inf (inf_le_left.trans hTM) inf_le_right) inf_le_left
  · exact (d.index_planeStabilizer T hTM i).trans hS
  · rwa [d.plane_normalizer_relIndex]

/-- The even index of the fixed-line pointwise stabilizer gives its local Sylow property. -/
theorem planeStabilizer_local_centralizer_index [Finite G]
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) (i : OrthogonalPlaneIndex)
    (hS : (setwise (orthogonalCoordinatePlane i)).relIndex (d.image T) = 2)
    (hC : 2 ∣ (pointwise (orthogonalCoordinatePlane i ⊓
      fixedVectors (d.image T ⊓ setwise (orthogonalCoordinatePlane i)))).index) :
    ¬ 2 ∣ (planeStabilizer T (d.plane i)).relIndex
      (M ⊓ centralizer (fixedPlane (d.plane i) (planeStabilizer T (d.plane i)) : Set G)) := by
  apply odd_local_index T hTM inf_le_left
    (le_inf (inf_le_left.trans hTM) (le_centralizer_iff.mp inf_le_right)) inf_le_left
  · exact (d.index_planeStabilizer T hTM i).trans hS
  · change 2 ∣ (M ⊓ centralizer
      (fixedPlane (d.plane i) (planeStabilizer T (d.plane i)) : Set G)).relIndex M
    rw [d.plane_fixed_eq_map (X := planeStabilizer T (d.plane i)) (inf_le_left.trans hTM) i,
      d.vector_centralizer_relIndex, d.image_planeStabilizer]
    exact hC

/-- The source module contains the entire central omega subgroup and has exponent two. -/
theorem centralInvolutions_eq_fixedPlane [Finite G] (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M)
    (d : NaturalOrthogonalAction M (localModule T M)) :
    centralInvolutions T = fixedPlane (localModule T M) T := by
  apply le_antisymm
  · exact le_inf (le_conjugateSpanBy _ _) (centralInvolutions_le_centralizer_sylow T)
  · intro z hz
    let _ := d.elementary
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mpr
    exact ⟨d.le_sylow T hTM (localModule_le T hTM) hz.1,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz.1, hz.2⟩

end NaturalOrthogonalAction
end CFSG.Quasithin.Chapter15.Section03

end
