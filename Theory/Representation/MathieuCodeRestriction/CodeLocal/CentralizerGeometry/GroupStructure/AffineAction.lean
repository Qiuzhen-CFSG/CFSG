module

public import Theory.Representation.MathieuCodeRestriction.CodeLocal.CentralizerGeometry.GroupStructure.AffineModel
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.CentralizerGeometry
public import Theory.Mathieu.M24.ChapterHStabilizers.OctadAction

/-!
# The native octad stabilizer is the full affine group

Choose one point outside the octad as origin. The elementary octad kernel
acts regularly on the complementary sixteen points, so evaluation at that
origin gives a crossed homomorphism. Combining it with the already proved
full GL4(2) conjugation action constructs a faithful affine action. Its
translations and linear image make it surjective.

The resulting group isomorphism carries each actual pointwise octad fixer
to translation by its existing binary coordinates. This is the marked affine
model needed for the involution supplement in Aschbacher (1994), 39.1 and
Aschbacher--Smith H.16.2(6), printed pp.402--403.
-/

public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24ChapterHStabilizers.OctadAction
open MathieuCode.CocodeOctad.Dynamics
open scoped Pointwise

namespace MathieuCode.OctadAffine
noncomputable section


private theorem exists_outside (O : Octad) : ∃ x : Fin 24, x ∉ O.val := by
  by_contra h
  push Not at h
  have he : O.val = Finset.univ := Finset.eq_univ_of_forall h
  have hc := m24Blocks_card _ O.property
  rw [he] at hc
  simp at hc

private def origin (O : Octad) : Fin 24 := Classical.choose (exists_outside O)
private theorem origin_outside (O : Octad) : origin O ∉ O.val :=
  Classical.choose_spec (exists_outside O)

private theorem image_outside (O : Octad) (g : octadStabilizer O) :
    g.val • origin O ∉ O.val := by
  intro h
  apply origin_outside O
  have he := MulAction.mem_stabilizer_finset.mp g.property (origin O)
  exact he.mp h

private theorem regular (O : Octad) (a b : octadPointwiseKernel O)
    (h : a.val • origin O = b.val • origin O) : a = b := by
  have hf : (b⁻¹ * a).val • origin O = origin O := by
    change (b.val⁻¹ * a.val) • origin O = origin O
    rw [mul_smul, h, inv_smul_smul]
  have he : (b⁻¹ * a).val = 1 := by
    by_contra hn
    exact origin_outside O ((octad_kernel_fixed_point_iff O _ (b⁻¹ * a).property hn _).mp hf)
  have he' : b⁻¹ * a = 1 := Subtype.ext he
  exact (inv_mul_eq_one.mp he').symm

private def displacement (O : Octad) (g : octadStabilizer O) : octadPointwiseKernel O :=
  Classical.choose (octad_kernel_transitive O (origin O) (g.val • origin O)
    (origin_outside O) (image_outside O g))

private theorem displacement_spec (O : Octad) (g : octadStabilizer O) :
    (displacement O g).val • origin O = g.val • origin O :=
  Classical.choose_spec (octad_kernel_transitive O (origin O) (g.val • origin O)
    (origin_outside O) (image_outside O g))

private theorem displacement_one (O : Octad) : displacement O 1 = 1 :=
  regular O _ _ (displacement_spec O 1)

private theorem displacement_mul (O : Octad) (g h : octadStabilizer O) :
    displacement O (g * h) = kernelConjugate O g (displacement O h) * displacement O g := by
  apply regular O
  rw [displacement_spec]
  change (g.val * h.val) • origin O =
    ((g.val * (displacement O h).val * g.val⁻¹) * (displacement O g).val) • origin O
  simp only [mul_smul, displacement_spec, inv_smul_smul]

/-- The native action as an affine map, after choosing one complementary point as origin. -/
def action (O : Octad) : octadStabilizer O →* AffineGroup where
  toFun g := AffineEquiv.ofLinearEquiv (linearAction O g) 0
    (pointwiseCoordinates O (displacement O g)).toAdd
  map_one' := by
    apply AffineEquiv.ext
    intro v
    simp [AffineEquiv.ofLinearEquiv_apply, displacement_one]
  map_mul' g h := by
    apply AffineEquiv.ext
    intro v
    change linearAction O (g * h) (v - 0) +
      (pointwiseCoordinates O (displacement O (g * h))).toAdd =
      linearAction O g (linearAction O h (v - 0) +
        (pointwiseCoordinates O (displacement O h)).toAdd - 0) +
      (pointwiseCoordinates O (displacement O g)).toAdd
    rw [displacement_mul, map_mul (pointwiseCoordinates O)]
    change linearAction O (g * h) (v - 0) +
      ((pointwiseCoordinates O (kernelConjugate O g (displacement O h))).toAdd +
      (pointwiseCoordinates O (displacement O g)).toAdd) = _
    rw [pointwiseCoordinates_conjugation, map_mul]
    simp only [sub_zero, LinearEquiv.mul_apply, map_add, add_assoc]

/-- Its linear part is exactly the already marked action on the octad kernel. -/
theorem action_linear (O : Octad) (g : octadStabilizer O) :
    (action O g).linear = linearAction O g := (rfl)

/-- Pointwise octad fixers act as the actual translations in these coordinates. -/
theorem action_kernel (O : Octad) (a : octadPointwiseKernel O) :
    action O ⟨a.val, kernel_le_stabilizer O a.property⟩ =
      AffineEquiv.constVAdd (ZMod 2) Space (pointwiseCoordinates O a).toAdd := by
  have hd : displacement O ⟨a.val, kernel_le_stabilizer O a.property⟩ = a :=
    regular O _ _ (displacement_spec O _)
  have ha : (⟨a.val, kernel_le_stabilizer O a.property⟩ : octadStabilizer O) ∈ Sporadic.Mathieu.M24ChapterHStabilizers.OctadAction.Core O := by
    have hmap : a.val ∈ (Sporadic.Mathieu.M24ChapterHStabilizers.OctadAction.Core O).map (octadStabilizer O).subtype := by
      rw [octad_core_map_eq_pointwise]
      exact a.property
    obtain ⟨b, hb, he⟩ := hmap
    have he' : b = ⟨a.val, kernel_le_stabilizer O a.property⟩ := Subtype.ext he
    exact he' ▸ hb
  have hl : linearAction O ⟨a.val, kernel_le_stabilizer O a.property⟩ = 1 :=
    MonoidHom.mem_ker.mp ((linearAction_ker O).symm ▸ ha)
  apply AffineEquiv.ext
  intro v
  change linearAction O _ (v - 0) + _ = _ + v
  rw [hl, hd]
  simp [add_comm]

/-- The affine action is faithful on the whole native octad stabilizer. -/
theorem action_injective (O : Octad) : Function.Injective (action O) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  have hg1 : action O g = 1 := hg
  have hl : linearAction O g = 1 := congrArg AffineEquiv.linear hg1
  have hcore : g ∈ Sporadic.Mathieu.M24ChapterHStabilizers.OctadAction.Core O := (linearAction_ker O) ▸ MonoidHom.mem_ker.mpr hl
  have hk : g.val ∈ octadPointwiseKernel O := by
    rw [← octad_core_map_eq_pointwise]
    exact Subgroup.mem_map_of_mem _ hcore
  have he := congrArg (fun f : AffineGroup => f 0) hg1
  rw [action_kernel O ⟨g.val, hk⟩] at he
  have hv : (pointwiseCoordinates O ⟨g.val, hk⟩).toAdd = 0 := by simpa using he
  have hk1 : (⟨g.val, hk⟩ : octadPointwiseKernel O) = 1 :=
    (pointwiseCoordinates O).injective (by simpa using hv)
  change g = 1
  apply Subtype.ext
  exact congrArg (fun a : octadPointwiseKernel O => a.val) hk1

/-- Every affine automorphism is realized by a native octad-stabilizer element. -/
theorem action_surjective (O : Octad) : Function.Surjective (action O) := by
  intro f
  obtain ⟨g, hg⟩ := linearAction_surjective O f.linear
  let w := f 0 - action O g 0
  let a := (pointwiseCoordinates O).symm (Multiplicative.ofAdd w)
  let k : octadStabilizer O := ⟨a.val, kernel_le_stabilizer O a.property⟩
  refine ⟨k * g, ?_⟩
  rw [map_mul]
  have hk : action O k = AffineEquiv.constVAdd (ZMod 2) Space w := by
    rw [action_kernel O a]
    exact congrArg (AffineEquiv.constVAdd (ZMod 2) Space)
      (congrArg Multiplicative.toAdd ((pointwiseCoordinates O).apply_symm_apply _))
  rw [hk]
  apply AffineEquiv.ext
  intro v
  change w + action O g v = f v
  have hgv : action O g v = f.linear v + action O g 0 := by
    have h := (action O g).map_vadd (0 : Space) v
    simpa only [vadd_eq_add, add_zero, action_linear, hg] using h
  have hfv : f v = f.linear v + f 0 := by
    simpa only [vadd_eq_add, add_zero] using f.map_vadd (0 : Space) v
  rw [hgv, hfv]
  dsimp [w]
  abel

/-- A genuine affine-group identification, compatible with native translations. -/
@[expose] def equiv (O : Octad) : octadStabilizer O ≃* AffineGroup :=
  MulEquiv.ofBijective (action O) ⟨action_injective O, action_surjective O⟩

end
end MathieuCode.OctadAffine
