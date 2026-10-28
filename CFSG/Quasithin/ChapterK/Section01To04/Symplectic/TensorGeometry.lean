module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Descent
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Equality.Source
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Equality.PointRoots
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorReduction
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Geometry and ratios of the descended symplectic tensor

Transport the actual plane-parabolic radical into the original component and
ambient group using the displayed tensor identification. It has rank 6s,
fixed dimension 4s, cubic action and ratio two, giving the upper cubic bound.
No fixed-space or actor conclusion is an input to these computations.

Native involution dimensions force diagram preservation. The outer estimates
then place every small-ratio actor in the component, and the literal Sylow
pointwise fixers exclude quadratic actors. Root intersections and the corrected
point-radical bound identify every equality actor with the plane radical.
Thus q > 2 = q̂, with every geometric premise discharged from the genuine source
hypotheses and an actual tensor identification. Recognition of that
identification remains separate. Source: Aschbacher–Smith, K.3.4.2,
printed pp.456–457 (PDF pp.467–468).
-/

@[expose] public section
open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair

namespace CFSG.Quasithin.ChapterK.Symplectic
open Representation Representation.BinaryOffender Theory.GroupTheory
open scoped ENNReal
variable {G V F : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
  [IsIrreducible (ρ.comp L.subtype)] [Field F]
  [Algebra (SchurField (ρ.comp L.subtype)) F]

/-- The literal plane radical transported into the original ambient group. -/
noncomputable def tensorPlaneActor {s : ℕ}
    (h : TensorIdentification (ρ.comp L.subtype) F s) : Subgroup G :=
  planeRadical.map (L.subtype.comp h.groupEquiv.symm.toMonoidHom)

omit [Finite G] in
theorem tensorPlaneActor_le_component {s : ℕ}
    (h : TensorIdentification (ρ.comp L.subtype) F s) : tensorPlaneActor ρ L h ≤ L := by
  rintro _ ⟨g, _, rfl⟩
  exact (h.groupEquiv.symm g).property

/-- The concrete K.3.4.2 actor, including the attained ratio. -/
theorem tensor_plane_actor {s : ℕ} (hs : 0 < s)
    (h : TensorIdentification (ρ.comp L.subtype) F s) :
    IsElementaryTwo (tensorPlaneActor ρ L h) ∧ IsCubic ρ (tensorPlaneActor ρ L h) ∧
      rank (tensorPlaneActor ρ L h) = 6 * s ∧
      Module.finrank (ZMod 2) (fixedSpace ρ (tensorPlaneActor ρ L h)) = 4 * s ∧
      fixedCodim ρ (tensorPlaneActor ρ L h) = 12 * s ∧
      actionRatio ρ (tensorPlaneActor ρ L h) = 2 := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField (ρ.comp L.subtype)) 2 := charP_of_injective_algebraMap
    (algebraMap (ZMod 2) (SchurField (ρ.comp L.subtype))).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap
    (algebraMap (SchurField (ρ.comp L.subtype)) F).injective 2
  let f : Sp F →* G := L.subtype.comp h.groupEquiv.symm.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp h.groupEquiv.symm.injective
  have helem : IsElementaryTwo (tensorPlaneActor ρ L h) := by
    let : IsElementaryAbelian 2 (planeRadical (F := F)) := planeRadical_elementary
    refine ⟨?_, IsElementaryAbelian.map f⟩
    intro hz
    apply (Natural.planeRadical_isElementaryTwo h.field_card (by omega)).1
    apply Subgroup.map_injective hf
    simpa only [tensorPlaneActor, f, Subgroup.map_bot] using hz
  have hcubic : IsCubic ρ (tensorPlaneActor ρ L h) := by
    rintro a ⟨a', ha, rfl⟩ b ⟨b', hb, rfl⟩ c ⟨c', hc, rfl⟩ v
    exact h.plane_cubic (ρ.comp L.subtype)
      _ (Subgroup.mem_map_of_mem _ ha) _ (Subgroup.mem_map_of_mem _ hb)
      _ (Subgroup.mem_map_of_mem _ hc) v
  have hrank : rank (tensorPlaneActor ρ L h) = 6 * s := by
    rw [tensorPlaneActor, rank_map_injective f hf, rank_planeRadical h.field_card]
    omega
  have hfixed : Module.finrank (ZMod 2) (fixedSpace ρ (tensorPlaneActor ρ L h)) = 4 * s := by
    rw [tensorPlaneActor, ← Subgroup.map_map, ← fixedSpace_comp_map]
    exact h.plane_fixed_finrank (ρ.comp L.subtype)
  have hcod : fixedCodim ρ (tensorPlaneActor ρ L h) = 12 * s := by
    have hh := fixedCodim_add_finrank ρ (tensorPlaneActor ρ L h)
    rw [hfixed, h.binary_finrank] at hh
    omega
  refine ⟨helem, hcubic, hrank, hfixed, hcod, ?_⟩
  have hs0 : (s : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  rw [actionRatio, hrank, hcod]
  push_cast
  rw [ENNReal.mul_div_mul_right _ _ hs0 (by simp)]
  rw [show (12 : ℝ≥0∞) = 2 * 6 by norm_num]
  exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)

/-- The upper cubic bound follows from an actual elementary actor. -/
theorem tensor_cubicRatio_le_two {s : ℕ} (hs : 0 < s)
    (h : TensorIdentification (ρ.comp L.subtype) F s) : cubicRatio ρ ≤ 2 := by
  obtain ⟨hA, hcube, _, _, _, hratio⟩ := tensor_plane_actor ρ L hs h
  rw [← hratio]
  exact iInf_le_of_le (tensorPlaneActor ρ L h) (iInf_le_of_le ⟨hA, hcube⟩ le_rfl)

omit [Finite G] in
/-- In a Sylow subgroup whose component intersection is identified with the
standard unipotent subgroup, the displayed equality actor lies in that Sylow. -/
theorem tensorPlaneActor_le_sylow {s : ℕ}
    (h : TensorIdentification (ρ.comp L.subtype) F s) (T : Sylow 2 G)
    (hT : ((T : Subgroup G).subgroupOf L).map h.groupEquiv.toMonoidHom = unipotent) :
    tensorPlaneActor ρ L h ≤ T := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField (ρ.comp L.subtype)) 2 := charP_of_injective_algebraMap
    (algebraMap (ZMod 2) (SchurField (ρ.comp L.subtype))).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap
    (algebraMap (SchurField (ρ.comp L.subtype)) F).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hp : planeRadical (F := F) ≤ unipotent := by
    rw [planeRadical_eq_wing]
    exact Subgroup.map_subtype_le _
  rintro _ ⟨g, hg, rfl⟩
  have hu := hp hg
  rw [← hT] at hu
  obtain ⟨l, hl, he⟩ := hu
  have he' : h.groupEquiv.symm g = l := by
    apply h.groupEquiv.injective
    simpa only [MulEquiv.apply_symm_apply, MulEquiv.coe_toMonoidHom] using he.symm
  change (h.groupEquiv.symm g).val ∈ T
  rw [he']
  exact hl

/-- The other parabolic radical in the original group. Its full fixed space
descends from the projective point tensor itself; this does not assert the
same fixed space for arbitrary subgroups of the radical. -/
noncomputable def tensorPointActor {s : ℕ}
    (h : TensorIdentification (ρ.comp L.subtype) F s) : Subgroup G :=
  SymplecticConjugatePair.pointRadical.map (L.subtype.comp h.groupEquiv.symm.toMonoidHom)

/-- The complete point radical has rank 6s, fixed dimension s and ratio 5/2.
The subgroup exclusion uses the separate bound of 3s, not this equality. -/
theorem tensor_point_actor {s : ℕ} (hs : 0 < s)
    (h : TensorIdentification (ρ.comp L.subtype) F s) :
    tensorPointActor ρ L h ≤ L ∧ IsElementaryTwo (tensorPointActor ρ L h) ∧
      rank (tensorPointActor ρ L h) = 6 * s ∧
      Module.finrank (ZMod 2) (fixedSpace ρ (tensorPointActor ρ L h)) = s ∧
      fixedCodim ρ (tensorPointActor ρ L h) = 15 * s ∧
      actionRatio ρ (tensorPointActor ρ L h) = (5 : ℝ≥0∞) / 2 := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField (ρ.comp L.subtype)) 2 := charP_of_injective_algebraMap
    (algebraMap (ZMod 2) (SchurField (ρ.comp L.subtype))).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap
    (algebraMap (SchurField (ρ.comp L.subtype)) F).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let f : Sp F →* G := L.subtype.comp h.groupEquiv.symm.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp h.groupEquiv.symm.injective
  have hrank : rank (tensorPointActor ρ L h) = 6 * s := by
    rw [tensorPointActor, rank_map_injective f hf, rank_pointRadical h.field_card]
    omega
  have helem : IsElementaryTwo (tensorPointActor ρ L h) := by
    let : IsElementaryAbelian 2 (SymplecticConjugatePair.pointRadical (F := F)) :=
      pointRadical_elementary
    refine ⟨?_, IsElementaryAbelian.map f⟩
    intro hz
    rw [hz, Representation.BinaryOffender.rank_bot] at hrank
    omega
  have hfixed : Module.finrank (ZMod 2) (fixedSpace ρ (tensorPointActor ρ L h)) = s := by
    rw [tensorPointActor, ← Subgroup.map_map, ← fixedSpace_comp_map]
    exact h.point_fixed_finrank (ρ.comp L.subtype)
  have hcod : fixedCodim ρ (tensorPointActor ρ L h) = 15 * s := by
    have hh := fixedCodim_add_finrank ρ (tensorPointActor ρ L h)
    rw [hfixed, h.binary_finrank] at hh
    omega
  refine ⟨?_, helem, hrank, hfixed, hcod, ?_⟩
  · rintro _ ⟨g, _, rfl⟩
    exact (h.groupEquiv.symm g).property
  · have hs0 : (s : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
    rw [actionRatio, hrank, hcod]
    push_cast
    rw [ENNReal.mul_div_mul_right _ _ hs0 (by simp)]
    rw [show (15 : ℝ≥0∞) = 5 * 3 by norm_num,
      show (6 : ℝ≥0∞) = 2 * 3 by norm_num]
    exact ENNReal.mul_div_mul_right _ _ (by norm_num) (by norm_num)

open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.InvolutionTypes

/-- The distinct native b₁/a₂ fixed dimensions rule out a diagram swap. -/
theorem TensorIdentification.preservesDiagram [L.Normal] {s : ℕ} (hs : 0 < s)
    (h : TensorIdentification (ρ.comp L.subtype) F s) (g : G) :
    PreservesDiagram (extensionAction L h.groupEquiv.symm g) := by
  exact h.preservesDiagram_of_native_fixed_dimensions hs
    (fun j hj => h.component_isB1_fixed_finrank ρ L j.val j.property hj)
    (fun j hj => h.component_isA2_fixed_finrank ρ L j.val j.property hj) g

variable {ρ L} {K : GroupClass} (hS : SourceHypothesis K ρ L)
  {s : ℕ} (hs : 0 < s) (h : TensorIdentification (ρ.comp L.subtype) F s)

include hS hs h

/-- The exact placement premise of the quadratic obstruction, with the
native dimensions supplied by the actual tensor calculation. -/
theorem tensor_source_elementary_le_component :
    ∀ A, IsElementaryTwo A → fixedCodim ρ A ≤ 2 * rank A → A ≤ L := by
  exact h.elementary_le_component hS hs
    (fun j hj => h.component_isB1_fixed_finrank ρ L j.val j.property hj)
    (fun j hj => h.component_isA2_fixed_finrank ρ L j.val j.property hj)

/-- The exact local premise of the quadratic obstruction, including the
literal displacement fixer inside the given ambient Sylow subgroup. -/
theorem tensor_source_involution_local_bounds :
    ∀ (T : Sylow 2 G) (j : G), j ∈ T → j ∈ L → orderOf j = 2 →
      Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers j)) ≤ 10 * s ∧
        rank (subspaceKernel ρ (LinearMap.range (displacement ρ j)) T) ≤ s := by
  let : L.Normal := by rw [← hS.fitting]; infer_instance
  exact h.involution_local_bounds hS (h.preservesDiagram ρ L hs)

/-- K.3.4.2's strict quadratic bound. Both geometric premises of the
published `TensorReduction` consumer are discharged here. -/
theorem tensor_source_quadraticRatio_gt_two : 2 < quadraticRatio ρ := by
  exact h.quadraticRatio_gt_two ρ hs
    (tensor_source_elementary_le_component hS hs h)
    (tensor_source_involution_local_bounds hS hs h)

/-- The attained plane-radical ratio and the equality argument give q̂ = 2. -/
theorem tensor_source_cubicRatio_eq_two : cubicRatio ρ = 2 := by
  exact le_antisymm (tensor_cubicRatio_le_two ρ L hs h)
    (tensor_source_cubicRatio_ge_two hS hs h)

/-- In every literally marked Sylow, the plane radical is the unique
elementary actor of ratio at most two. -/
theorem tensor_source_marked_actor_iff (T : Sylow 2 G)
    (hT : ((T : Subgroup G).subgroupOf L).map h.groupEquiv.toMonoidHom = unipotent)
    (A : Subgroup G) :
    (IsElementaryTwo A ∧ A ≤ T ∧ actionRatio ρ A ≤ 2) ↔
      A = tensorPlaneActor ρ L h := by
  constructor
  · rintro ⟨hA, hAT, hsmall⟩
    exact tensor_source_marked_actor_eq hS hs h T hT hA hAT hsmall
  · rintro rfl
    obtain ⟨hA, _, _, _, _, hr⟩ := tensor_plane_actor ρ L hs h
    exact ⟨hA, tensorPlaneActor_le_sylow ρ L h T hT, hr.le⟩

/-- The numerical and equality-actor conclusions of K.3.4.2 from the genuine
source hypotheses and a displayed scalar-extension tensor identification.
The equality actor is the literal transported plane radical, and its fixed
space comes from the vector two-plane tensor, of defining-field dimension four. -/
theorem tensor_source_geometry :
    Module.finrank (ZMod 2) V = 16 * s ∧
      2 < quadraticRatio ρ ∧ cubicRatio ρ = 2 ∧
      ∀ (T : Sylow 2 G),
        ((T : Subgroup G).subgroupOf L).map h.groupEquiv.toMonoidHom = unipotent →
        tensorPlaneActor ρ L h ≤ T ∧
          IsElementaryTwo (tensorPlaneActor ρ L h) ∧
          IsCubic ρ (tensorPlaneActor ρ L h) ∧
          rank (tensorPlaneActor ρ L h) = 6 * s ∧
          Module.finrank (ZMod 2) (fixedSpace ρ (tensorPlaneActor ρ L h)) = 4 * s ∧
          fixedCodim ρ (tensorPlaneActor ρ L h) = 12 * s ∧
          actionRatio ρ (tensorPlaneActor ρ L h) = 2 ∧
          ∀ A : Subgroup G, IsElementaryTwo A → A ≤ T → actionRatio ρ A ≤ 2 →
            A = tensorPlaneActor ρ L h := by
  refine ⟨h.binary_finrank, tensor_source_quadraticRatio_gt_two hS hs h,
    tensor_source_cubicRatio_eq_two hS hs h, ?_⟩
  intro T hT
  obtain ⟨hA, hc, hr, hf, hd, hratio⟩ := tensor_plane_actor ρ L hs h
  exact ⟨tensorPlaneActor_le_sylow ρ L h T hT, hA, hc, hr, hf, hd, hratio,
    fun A hA hAT hsmall => (tensor_source_marked_actor_iff hS hs h T hT A).mp
      ⟨hA, hAT, hsmall⟩⟩

end CFSG.Quasithin.ChapterK.Symplectic
