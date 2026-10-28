module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.Geometry
import Mathlib.Tactic.Group

/-!
# The obstruction to lifting the chosen involution centralizer

An element centralizing the projective image of w has commutator with w in
the central four. This commutator is a crossed homomorphism. If w centralizes
the covering kernel, the defect is constant on every projective fiber; its
vanishing characterizes the actual centralizer image. In particular, multiplying
a representative by a covering-kernel element cannot repair a nonzero defect.

The marked normalizer supplies precisely this kernel-centralizing hypothesis
for its chosen graph-field product. None of the selected lifts is replaced.

Source: Aschbacher--Smith, 15.3.38, printed pp.1136--1137, manuscript of
1 March 2004. The value of the defect in the four-cover remains a model input.
-/

public section
namespace Matrix.PSL3Four.ExtendedCentralizer
open Subgroup
variable {I : Type*} [Group I] {L : Subgroup I} [L.Normal]

/-- The full standard projective centralizer of the specified image of w. -/
@[expose] noncomputable def projectiveCentralizer (d : Overgroup L) (w : I) :
    Subgroup (MulAut PSL) :=
  PSL3.OuterSolvable.standard F ⊓ centralizer ({projectiveAction L d.cover w} : Set (MulAut PSL))

/-- Elements centralizing w after descent, before requiring actual commutation. -/
@[expose] noncomputable def projectiveCentralizerPreimage (d : Overgroup L) (w : I) : Subgroup I :=
  (centralizer ({projectiveAction L d.cover w} : Set (MulAut PSL))).comap
    (projectiveAction L d.cover)

theorem projectiveCentralizerPreimage_map (d : Overgroup L) (w : I) :
    (projectiveCentralizerPreimage d w).map (projectiveAction L d.cover) =
      projectiveCentralizer d w := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨d.full_action ▸ ⟨x, rfl⟩, hx⟩
  · rintro ⟨ha, hc⟩
    rw [← d.full_action] at ha
    obtain ⟨x, rfl⟩ := ha
    exact ⟨x, hc, rfl⟩

private theorem liftDefect_mem (d : Overgroup L) (w : I)
    (x : projectiveCentralizerPreimage d w) :
    (x : I) * w * (x : I)⁻¹ * w⁻¹ ∈ (center L).map L.subtype := by
  rw [← d.projectiveAction_ker]
  change projectiveAction L d.cover ((x : I) * w * (x : I)⁻¹ * w⁻¹) = 1
  have hx := mem_centralizer_singleton_iff.mp x.property
  simp only [map_mul, map_inv]
  rw [hx]
  group

/-- The literal central commutator obstructing the lift of a projective centralizer.
It is generally a crossed homomorphism, not a homomorphism. -/
noncomputable def centralizerLiftDefect (d : Overgroup L) (w : I)
    (x : projectiveCentralizerPreimage d w) : (center L).map L.subtype :=
  ⟨(x : I) * w * (x : I)⁻¹ * w⁻¹, liftDefect_mem d w x⟩

theorem centralizerLiftDefect_val (d : Overgroup L) (w : I)
    (x : projectiveCentralizerPreimage d w) :
    (centralizerLiftDefect d w x : I) = (x : I) * w * (x : I)⁻¹ * w⁻¹ := by rfl

theorem centralizerLiftDefect_eq_one_iff (d : Overgroup L) (w : I)
    (x : projectiveCentralizerPreimage d w) :
    centralizerLiftDefect d w x = 1 ↔ (x : I) ∈ centralizerIn w := by
  rw [Subtype.ext_iff]
  change (x : I) * w * (x : I)⁻¹ * w⁻¹ = 1 ↔ _
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  exact mem_centralizer_singleton_iff.symm

theorem centralizerLiftDefect_mul (d : Overgroup L) (w : I)
    (x y : projectiveCentralizerPreimage d w) :
    (centralizerLiftDefect d w (x * y) : I) =
      (x : I) * (centralizerLiftDefect d w y : I) * (x : I)⁻¹ *
        (centralizerLiftDefect d w x : I) := by
  change ((x : I) * y) * w * ((x : I) * y)⁻¹ * w⁻¹ =
    (x : I) * ((y : I) * w * (y : I)⁻¹ * w⁻¹) * (x : I)⁻¹ *
      ((x : I) * w * (x : I)⁻¹ * w⁻¹)
  group

/-- When w centralizes the covering kernel, changing a lift cannot repair
its commutator defect. This is the reason centralizer surjectivity needs proof. -/
theorem centralizerLiftDefect_eq_of_projective_eq (d : Overgroup L) (w : I)
    (hw : w ∈ centralizer ((center L).map L.subtype : Set I))
    (x y : projectiveCentralizerPreimage d w)
    (hxy : projectiveAction L d.cover (x : I) = projectiveAction L d.cover (y : I)) :
    centralizerLiftDefect d w x = centralizerLiftDefect d w y := by
  have hz : (y : I)⁻¹ * (x : I) ∈ (center L).map L.subtype := by
    rw [← d.projectiveAction_ker]
    change projectiveAction L d.cover ((y : I)⁻¹ * (x : I)) = 1
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have hc := hw _ hz
  apply Subtype.ext
  change (x : I) * w * (x : I)⁻¹ * w⁻¹ = (y : I) * w * (y : I)⁻¹ * w⁻¹
  calc
    _ = (y : I) * (((y : I)⁻¹ * (x : I)) * w) * (x : I)⁻¹ * w⁻¹ := by group
    _ = (y : I) * (w * ((y : I)⁻¹ * (x : I))) * (x : I)⁻¹ * w⁻¹ := by rw [hc]
    _ = _ := by group

/-- Exact membership in the image of the actual centralizer, for each chosen
projective lift. No lift is replaced by a standard representative. -/
theorem projective_mem_centralizerImage_iff (d : Overgroup L) (w : I)
    (hw : w ∈ centralizer ((center L).map L.subtype : Set I))
    (x : projectiveCentralizerPreimage d w) :
    projectiveAction L d.cover (x : I) ∈
        (centralizerIn w).map (projectiveAction L d.cover) ↔
      centralizerLiftDefect d w x = 1 := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hy' : y ∈ projectiveCentralizerPreimage d w := by
      change projectiveAction L d.cover y ∈ centralizer ({projectiveAction L d.cover w} : Set _)
      apply mem_centralizer_singleton_iff.mpr
      simpa only [map_mul] using congrArg (projectiveAction L d.cover)
        (mem_centralizer_singleton_iff.mp hy)
    rw [centralizerLiftDefect_eq_of_projective_eq d w hw x ⟨y, hy'⟩ hxy.symm]
    exact (centralizerLiftDefect_eq_one_iff d w ⟨y, hy'⟩).mpr hy
  · intro hx
    exact ⟨x, (centralizerLiftDefect_eq_one_iff d w x).mp hx, rfl⟩

/-- The supplied normalizer geometry has precisely the central-kernel hypothesis
needed to use the lift-defect criterion. -/
theorem NormalizerGeometry.graphField_mem_centerCentralizer {d : Overgroup L}
    (n : NormalizerGeometry d) :
    n.graphFieldI ∈ centralizer ((center L).map L.subtype : Set I) := by
  exact n.graphField_centralizes_center

/-- The marked product acts nontrivially on the linear three-factor, so its
projective image cannot be the identity. -/
theorem NormalizerGeometry.graphField_projective_ne_one {d : Overgroup L}
    (n : NormalizerGeometry d) : projectiveAction L d.cover n.graphFieldI ≠ 1 := by
  intro hw
  have hwC : n.graphFieldI ∈ centralizer (L : Set I) := by
    rw [← ExtendedCentralizer.projectiveAction_ker d.cover]
    exact hw
  let x := n.coordinates.symm (rotation, 1)
  have hxL : n.inclusion x ∈ L := by
    have hm : (rotation, 1) ∈
        (((n.X : Subgroup n.YS) ⊓ L.comap n.YS.subtype).subgroupOf
          (normalizer (n.X : Set n.YS))).map n.coordinates.toMonoidHom := by
      rw [n.linear_coordinates]
      exact ⟨mem_zpowers _, one_mem _⟩
    obtain ⟨y, hy, he⟩ := hm
    have hyx : y = x := n.coordinates.injective (he.trans (n.coordinates.apply_symm_apply _).symm)
    exact (hyx ▸ hy).2
  have hi : Function.Injective n.inclusion := n.YS.subtype_injective.comp
    (normalizer (n.X : Set n.YS)).subtype_injective
  have hh : n.inclusion (x * (n.tau * n.field)) =
      n.inclusion ((n.tau * n.field) * x) := by
    simpa only [map_mul, NormalizerGeometry.graphFieldI, NormalizerGeometry.tauI,
      NormalizerGeometry.fieldI] using hwC (n.inclusion x) hxL
  have hc := congrArg n.coordinates (hi hh)
  simp only [map_mul, n.tau_coordinates, n.field_coordinates,
    show n.coordinates x = (rotation, 1) from n.coordinates.apply_symm_apply _] at hc
  have he : ((1 : SymmetricThree), reflection) * (reflection, reflection) = (reflection, 1) := by decide
  rw [he] at hc
  exact (by decide : (rotation, (1 : SymmetricThree)) * (reflection, 1) ≠
    (reflection, 1) * (rotation, 1)) hc
end Matrix.PSL3Four.ExtendedCentralizer
