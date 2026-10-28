module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.HomogeneousFibres.Scalars
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.Geometry

/-!
# Coherent natural-plane coordinates in the homogeneous case

The same-orientation marking transports the original natural submodule into
exactly the quotient's matrix coordinates. Its Q-fixed space is the coordinate
hyperplane, whose shear parameters and vectors are both identified with F² by
inserting a zero at the omitted coordinate. Extending SL₂ by the identity on
that coordinate gives actors in the literal K, with matching natural action
and direct conjugation on Q. The original vectors with coordinates c e_j are
fixed by all of K, and their shear displacements are exactly c times the
parameter vector.

This constructs every field of `NaturalPlaneCoordinates` and applies scalar
rigidity to obtain the displacement-realization premise of the homogeneous
fibre proof. No field-degree restriction, quadraticity, or fixed-lift premise
is needed; in particular the construction includes F₄. Only the original
natural submodule is given field coordinates, not the extension V.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.9(1),
printed pp.93–94 (PDF pp.104–105), the homogeneous natural-module case.
-/

@[expose] public section

open Representation Representation.BinaryOffender Matrix
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
open QuasisimpleSource
open CFSG.Quasithin.ChapterK.Linear.Natural

namespace LargeFieldComplements.Homogeneous.CoordinateConstruction

set_option backward.isDefEq.respectTransparency false

private noncomputable def ins (F : BinaryField) (j : Fin 3) :
    (Fin 2 → F.Carrier) ≃ₗ[F.Carrier] coordinateHyperplane F 3 j where
  toFun t := ⟨j.insertNth 0 t, by simp⟩
  invFun w := fun i => w.val (j.succAbove i)
  left_inv t := by ext i; simp
  right_inv w := by
    apply Subtype.ext
    change j.insertNth 0 (fun i => w.val (j.succAbove i)) = w.val
    apply (Fin.insertNth_eq_iff).mpr
    exact ⟨w.property.symm, rfl⟩
  map_add' t u := by
    apply Subtype.ext
    change j.insertNth 0 (t + u) =
      j.insertNth (α := fun _ => F.Carrier) 0 t + j.insertNth (α := fun _ => F.Carrier) 0 u
    apply Fin.insertNth_eq_iff.mpr
    simp [Fin.removeNth, funext_iff]
  map_smul' c t := by
    apply Subtype.ext
    change j.insertNth 0 (c • t) = c • j.insertNth 0 t
    apply Fin.insertNth_eq_iff.mpr
    simp [Fin.removeNth, funext_iff]

private noncomputable def block (F : BinaryField) (j : Fin 3)
    (g : SpecialLinearGroup (Fin 2) F.Carrier) : SpecialLinearGroup (Fin 3) F.Carrier :=
  ⟨j.insertNth (Pi.single j 1) (fun r => j.insertNth 0 (g.val r)), by
    change Matrix.det (j.insertNth (Pi.single j 1) (fun r => j.insertNth 0 (g.val r)) :
      Matrix (Fin 3) (Fin 3) F.Carrier) = 1
    rw [Matrix.det_fin_three]
    have h := g.property
    rw [Matrix.det_fin_two] at h
    fin_cases j <;>
      simpa [Fin.insertNth, Fin.succAboveCases,
        Fin.succAbove] using h⟩

private lemma block_apply (F : BinaryField) (j : Fin 3)
    (g : SpecialLinearGroup (Fin 2) F.Carrier) (v : Fin 3 → F.Carrier) :
    linearNatural F 3 (block F j g) v =
      j.insertNth (v j) (linearNatural F 2 g (fun i => v (j.succAbove i))) := by
  change (block F j g).val.mulVec v =
    j.insertNth (v j) (g.val.mulVec (fun i => v (j.succAbove i)))
  apply Fin.eq_insertNth_iff.mpr
  constructor
  · change (block F j g).val j ⬝ᵥ v = v j
    simp only [block, Fin.insertNth_apply_same, single_dotProduct, one_mul]
  · funext r
    change (block F j g).val (j.succAbove r) ⬝ᵥ v = _
    simp only [block, Fin.insertNth_apply_succAbove]
    rw [dotProduct, Fin.sum_univ_succAbove _ j]
    simp only [Fin.insertNth_apply_same, zero_mul, Fin.insertNth_apply_succAbove, zero_add]
    rfl

private lemma block_coord (F : BinaryField) (j : Fin 3)
    (g : SpecialLinearGroup (Fin 2) F.Carrier) (v : Fin 3 → F.Carrier) :
    linearNatural F 3 (block F j g) v j = v j := by
  rw [block_apply]
  simp

private lemma block_plane (F : BinaryField) (j : Fin 3)
    (g : SpecialLinearGroup (Fin 2) F.Carrier) (t : Fin 2 → F.Carrier) :
    linearNatural F 3 (block F j g) (ins F j t) = ins F j (linearNatural F 2 g t) := by
  change linearNatural F 3 (block F j g) (j.insertNth 0 t) = j.insertNth 0 _
  rw [block_apply]
  simp

private lemma block_line (F : BinaryField) (j : Fin 3)
    (g : SpecialLinearGroup (Fin 2) F.Carrier) (c : F.Carrier) :
    linearNatural F 3 (block F j g) (Pi.single j c) = Pi.single j c := by
  rw [block_apply]
  apply Fin.insertNth_eq_iff.mpr
  constructor
  · rfl
  · have hz : (fun i : Fin 2 => (Pi.single j c : Fin 3 → F.Carrier) (j.succAbove i)) = 0 := by
      ext i
      simp
    rw [hz, map_zero]
    ext i
    simp [Fin.removeNth]

private lemma block_conjugate (F : BinaryField) (j : Fin 3)
    (g : SpecialLinearGroup (Fin 2) F.Carrier) (t : Fin 2 → F.Carrier) :
    shear F 3 j (ins F j (linearNatural F 2 g t)) =
      block F j g * shear F 3 j (ins F j t) * (block F j g)⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply natural_injective F 3
  apply LinearMap.ext
  intro v
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    shear_apply, shear_apply, block_coord]
  change specialLinearNatural 3 (block F j g) v +
      v j • (ins F j (linearNatural F 2 g t)).val =
    specialLinearNatural 3 (block F j g) (v + v j • (ins F j t).val)
  rw [map_add, map_smul]
  rw [show specialLinearNatural 3 (block F j g) (ins F j t) =
    (ins F j (linearNatural F 2 g t)).val from block_plane F j g t]

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F 3 ρ} (m : QuotientCoordinates d) (j : Fin 3)

private noncomputable def aligned : d.space.toSubmodule ≃ₗ[ZMod 2] (Fin 3 → F.Carrier) :=
  d.natural.linearEquiv.trans (LinearEquiv.ofBijective
    (linearNatural F 3 m.basisChange) ((linearNatural F 3).apply_bijective _))

private lemma aligned_apply (u : d.space.toSubmodule) :
    aligned m u = linearNatural F 3 m.basisChange (d.natural.linearEquiv u) := rfl

variable (hmark : ∀ g, m.action.groupEquiv g =
  m.basisChange * d.natural.groupEquiv g * m.basisChange⁻¹)

include hmark in
private lemma aligned_intertwines (g : G) (u : d.space.toSubmodule) :
    aligned m (d.space.toRepresentation g u) =
      linearNatural F 3 (m.action.groupEquiv g) (aligned m u) := by
  rw [aligned_apply, d.natural.intertwines, aligned_apply, hmark]
  simp only [map_mul, Module.End.mul_apply]
  rw [Representation.inv_self_apply]

include hmark in
private lemma aligned_fixed_iff (u : d.space.toSubmodule) :
    (u : V) ∈ fixedSpace ρ (m.Q j) ↔ aligned m u ∈ coordinateHyperplane F 3 j := by
  constructor
  · intro hu
    have hh : aligned m u ∈ fixedSpace (linearNatural F 3)
        (hyperplaneCentralizer F 3 j) := by
      intro a
      let g := m.action.groupEquiv.symm a
      have hg : g ∈ m.Q j := (m.largeField_mem_Q j g).mpr (by
        simpa only [g, MulEquiv.apply_symm_apply] using a.property)
      have hu' : d.space.toRepresentation g u = u := Subtype.ext (hu ⟨g, hg⟩)
      have he := congrArg (aligned m) hu'
      rw [aligned_intertwines m hmark] at he
      change linearNatural F 3 a (aligned m u) = aligned m u
      simpa only [g, MulEquiv.apply_symm_apply] using he
    rw [subgroup_fixedSpace F 3 j le_rfl
      (hyperplaneCentralizer_elementary F 3 j (by decide)).1] at hh
    exact hh
  · intro hu g
    have hg := (m.largeField_mem_Q j g).mp g.property
    have he : d.space.toRepresentation g u = u := by
      apply (aligned m).injective
      rw [aligned_intertwines m hmark]
      exact hg.2 _ hu
    exact congrArg Subtype.val he

private noncomputable def fixedEquiv :
    ↥(d.space.toSubmodule ⊓ fixedSpace ρ (m.Q j)) ≃ₗ[ZMod 2]
      coordinateHyperplane F 3 j where
  toFun w := ⟨aligned m ⟨w, w.property.1⟩,
    (aligned_fixed_iff m j hmark _).mp w.property.2⟩
  invFun w := ⟨(aligned m).symm w, ((aligned m).symm w).property,
    (aligned_fixed_iff m j hmark _).mpr (by
      rw [LinearEquiv.apply_symm_apply]; exact w.property)⟩
  left_inv w := by
    apply Subtype.ext
    exact congrArg (fun z : d.space.toSubmodule => (z : V))
      ((aligned m).symm_apply_apply ⟨w, w.property.1⟩)
  right_inv w := by
    apply Subtype.ext
    exact (aligned m).apply_symm_apply w
  map_add' w z := by
    apply Subtype.ext
    change aligned m (⟨w, w.property.1⟩ + ⟨z, z.property.1⟩) = _
    exact map_add (aligned m) _ _
  map_smul' c w := by
    apply Subtype.ext
    change aligned m (c • (⟨w, w.property.1⟩ : d.space.toSubmodule)) = _
    exact map_smul (aligned m) _ _

private noncomputable def parameters : (Fin 2 → F.Carrier) ≃+ Additive (m.Q j) :=
  AddEquiv.ofBijective
    ({ toFun := fun t => Additive.ofMul ⟨m.action.groupEquiv.symm (shear F 3 j (ins F j t)),
         (m.largeField_mem_Q j _).mpr (by
           rw [m.action.groupEquiv.apply_symm_apply]
           exact shear_mem F 3 j _)⟩
       map_zero' := by
         apply Additive.toMul.injective
         apply Subtype.ext
         simp only [map_zero, shear_zero, map_one]
         rfl
       map_add' := by
         intro t u
         apply Additive.toMul.injective
         apply Subtype.ext
         change m.action.groupEquiv.symm (shear F 3 j (ins F j (t + u))) =
           m.action.groupEquiv.symm (shear F 3 j (ins F j t)) *
             m.action.groupEquiv.symm (shear F 3 j (ins F j u))
         rw [map_add, shear_add, map_mul] } :
      (Fin 2 → F.Carrier) →+ Additive (m.Q j))
    ⟨by
      intro t u h
      apply (ins F j).injective
      apply shear_injective F 3 j
      apply m.action.groupEquiv.symm.injective
      exact congrArg (fun x : Additive (m.Q j) => (x.toMul : G)) h,
    by
      intro x
      obtain ⟨w, hw⟩ := centralizer_eq_shear F 3 j
        ((m.largeField_mem_Q j x.toMul).mp x.toMul.property)
      refine ⟨(ins F j).symm w, ?_⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      change m.action.groupEquiv.symm (shear F 3 j (ins F j ((ins F j).symm w))) = _
      rw [LinearEquiv.apply_symm_apply, hw, MulEquiv.symm_apply_apply]⟩

private lemma parameters_mark (t : Fin 2 → F.Carrier) :
    m.action.groupEquiv (parameters m j t).toMul = shear F 3 j (ins F j t) :=
  m.action.groupEquiv.apply_symm_apply _

private noncomputable def actor (g : SpecialLinearGroup (Fin 2) F.Carrier) : G :=
  m.action.groupEquiv.symm (block F j g)

private lemma actor_mem (g : SpecialLinearGroup (Fin 2) F.Carrier) : actor m j g ∈ m.K j := by
  have ha : m.action.groupEquiv (actor m j g) = block F j g :=
    m.action.groupEquiv.apply_symm_apply _
  constructor
  · intro z
    change d.space.quotientRepresentation (actor m j g) z ∈ m.axis j ↔ z ∈ m.axis j
    rw [m.largeField_mem_axis, m.largeField_mem_axis, m.action.intertwines, ha, block_coord]
  · refine ⟨Subgroup.mem_top _, ?_⟩
    intro z hz
    obtain ⟨c, hc⟩ := (m.largeField_mem_line j z).mp hz
    apply m.action.linearEquiv.injective
    rw [m.action.intertwines, ha, ← hc]
    have hs : c • (Pi.single j (1 : F.Carrier)) = Pi.single j c := by
      ext i
      by_cases hi : i = j <;> simp [hi]
    rw [hs, block_line]

private lemma parameters_conjugate (g : SpecialLinearGroup (Fin 2) F.Carrier)
    (t : Fin 2 → F.Carrier) :
    ((parameters m j (linearNatural F 2 g t)).toMul : G) =
      actor m j g * (parameters m j t).toMul * (actor m j g)⁻¹ := by
  apply m.action.groupEquiv.injective
  rw [parameters_mark, map_mul, map_mul, map_inv, parameters_mark]
  change shear F 3 j (ins F j (linearNatural F 2 g t)) =
    m.action.groupEquiv (m.action.groupEquiv.symm (block F j g)) *
      shear F 3 j (ins F j t) *
      (m.action.groupEquiv (m.action.groupEquiv.symm (block F j g)))⁻¹
  rw [MulEquiv.apply_symm_apply]
  exact block_conjugate F j g t

private noncomputable def plane :
    ↥(d.space.toSubmodule ⊓ fixedSpace ρ (m.Q j)) ≃ₗ[ZMod 2] (Fin 2 → F.Carrier) :=
  (fixedEquiv m j hmark).trans ((ins F j).symm.restrictScalars (ZMod 2))

private lemma plane_coordinates (w : ↥(d.space.toSubmodule ⊓ fixedSpace ρ (m.Q j))) :
    (ins F j (plane m j hmark w) : Fin 3 → F.Carrier) = aligned m ⟨w, w.property.1⟩ := by
  exact congrArg Subtype.val ((ins F j).apply_symm_apply (fixedEquiv m j hmark w))

private lemma plane_intertwines (g : SpecialLinearGroup (Fin 2) F.Carrier)
    (w w' : ↥(d.space.toSubmodule ⊓ fixedSpace ρ (m.Q j)))
    (hw : (w' : V) = ρ (actor m j g) w) :
    plane m j hmark w' = linearNatural F 2 g (plane m j hmark w) := by
  apply (ins F j).injective
  apply Subtype.ext
  rw [plane_coordinates, ← block_plane, plane_coordinates]
  have he : (⟨w', w'.property.1⟩ : d.space.toSubmodule) =
      d.space.toRepresentation (actor m j g) ⟨w, w.property.1⟩ := Subtype.ext hw
  rw [he, aligned_intertwines m hmark]
  simp only [actor, MulEquiv.apply_symm_apply]

private noncomputable def lineLift (c : F.Carrier) : V :=
  (aligned m).symm (Pi.single j c)

private lemma lineLift_mem (c : F.Carrier) : lineLift m j c ∈ d.space.toSubmodule :=
  ((aligned m).symm (Pi.single j c)).property

include hmark in
private lemma lineLift_fixed (c : F.Carrier) : lineLift m j c ∈ fixedSpace ρ (m.K j) := by
  intro k
  have hz : m.action.linearEquiv.symm (Pi.single j c) ∈ m.line j := by
    apply (m.largeField_mem_line j _).mpr
    refine ⟨c, ?_⟩
    rw [LinearEquiv.apply_symm_apply]
    ext i
    by_cases hi : i = j <;> simp [hi]
  have hk := congrArg m.action.linearEquiv (k.property.2.2 _ hz)
  rw [m.action.intertwines, LinearEquiv.apply_symm_apply] at hk
  have he : d.space.toRepresentation k ((aligned m).symm (Pi.single j c)) =
      (aligned m).symm (Pi.single j c) := by
    apply (aligned m).injective
    rw [aligned_intertwines m hmark, LinearEquiv.apply_symm_apply]
    exact hk
  exact congrArg Subtype.val he

private lemma displacement (c : F.Carrier) (t : Fin 2 → F.Carrier) :
    ρ (parameters m j t).toMul (lineLift m j c) - lineLift m j c =
      ((plane m j hmark).symm (c • t) : V) := by
  have he : d.space.toRepresentation (parameters m j t).toMul
        ((aligned m).symm (Pi.single j c)) - (aligned m).symm (Pi.single j c) =
      (aligned m).symm (ins F j (c • t)) := by
    apply (aligned m).injective
    rw [map_sub, aligned_intertwines m hmark,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, parameters_mark,
      shear_apply, Pi.single_eq_same, add_sub_cancel_left]
    exact (congrArg Subtype.val ((ins F j).map_smul c t)).symm
  exact congrArg Subtype.val he

private noncomputable def coordinates : NaturalPlaneCoordinates ρ (m.K j) (m.Q j) d.space F where
  parameters := parameters m j
  plane := plane m j hmark
  actor := actor m j
  actor_mem := actor_mem m j
  conjugate := parameters_conjugate m j
  intertwines := plane_intertwines m j hmark
  lineLift := lineLift m j
  lineLift_mem := lineLift_mem m j
  lineLift_fixed := lineLift_fixed m j hmark
  displacement := displacement m j hmark

end LargeFieldComplements.Homogeneous.CoordinateConstruction

namespace QuotientCoordinates
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F 3 ρ} (m : QuotientCoordinates d) (j : Fin 3)

/-- The same-orientation marking supplies the actual coherent plane, shear
parameters, SL₂ actors, and original fixed line vectors, over every binary field. -/
theorem homogeneous_naturalPlaneCoordinates
    (hmark : ∀ g, m.action.groupEquiv g =
      m.basisChange * d.natural.groupEquiv g * m.basisChange⁻¹) :
    Nonempty (LargeFieldComplements.Homogeneous.NaturalPlaneCoordinates
      ρ (m.K j) (m.Q j) d.space F) :=
  ⟨LargeFieldComplements.Homogeneous.CoordinateConstruction.coordinates m j hmark⟩

/-- Discharge the natural-displacement-realization premise used by the homogeneous
fibre argument, through the literal Q parameters and direct-conjugation action. -/
theorem homogeneous_naturalDisplacementRealization
    (hmark : ∀ g, m.action.groupEquiv g =
      m.basisChange * d.natural.groupEquiv g * m.basisChange⁻¹) :
    LargeFieldComplements.Homogeneous.NaturalDisplacementRealization
      ρ (m.K j) (m.Q j) d.space := by
  obtain ⟨c⟩ := m.homogeneous_naturalPlaneCoordinates j hmark
  exact LargeFieldComplements.Homogeneous.realization_of_marked_planes c

end QuotientCoordinates
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
