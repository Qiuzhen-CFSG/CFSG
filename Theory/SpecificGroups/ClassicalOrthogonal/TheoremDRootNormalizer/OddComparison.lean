/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.ScalarQuotients
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.Basic
public import Theory.SpecificGroups.PSp4Three.ProjectiveGeometry
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Algebra.CharP.Two

/-!
# The actual odd orthogonal–symplectic comparison in characteristic two

Projection away from the polar radical of `∑ xᵢ yᵢ + z²` embeds its full
isometry group in the existing symplectic matrix group. Over a perfect field,
every symplectic transvection lifts to a Siegel generator: lift its direction
to a singular vector using square roots, and use a multiple of the radical
vector as the Siegel parameter. Transvection generation makes the restricted
map from the actual elementary Omega group surjective. Both projective
kernels are trivial in characteristic two.

The result identifies the independently defined carriers by multiplicative
equivalence; no order, simplicity, or family-identification premise is used.
This treats the odd orthogonal aliases in the Lie-family branch of Theorem D,
with the classical conventions of GLS3 §2.7.

Adapted from Gerald Höhn's ATLAS at revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`,
`Atlas/LinearGroups/Orthogonal/{EvenProjection,EvenComparison,EvenGeneration}.lean`.
CFSG's elementary carrier and previously ported symplectic matrix group are
used directly. The explicit full-group square-root lift is unnecessary:
transvection generation already proves surjectivity on the elementary group.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.TheoremDRootNormalizer
universe u
variable {n : ℕ} {F : Type u} [Field F] [CharP F 2]

theorem polarD_eq_symplectic (x y : VectorD n F) :
    (formD n F).polarBilin x y = Matrix.PSp4Three.form x y := by
  rw [polarD_apply, Matrix.PSp4Three.form_apply]
  simp only [CharTwo.sub_eq_add]
  congr 1
  funext i
  ring

/-- Every full quadratic isometry fixes the distinguished radical vector itself. -/
theorem even_fix_z (g : Theory.AlgebraicGroup.quadraticIsometrySubgroup (formB n F)) : g.val z = z := by
  have hp : ∀ w, (formB n F).polarBilin (g.val z) w = 0 := by
    intro w
    have h := ClassicalOrthogonal.Quadratic.isometry_between_polar (formB n F) (formB n F)
      (ReflectionGeneration.isometryCarrierEquiv _ g) z (g.val.symm w)
    change (formB n F).polarBilin (g.val z) (g.val (g.val.symm w)) = _ at h
    rw [g.val.apply_symm_apply] at h
    rw [h]
    simp only [polarB_apply, z, map_zero, LinearMap.zero_apply, CharTwo.two_eq_zero,
      zero_mul, add_zero]
  obtain ⟨a, ha⟩ := (polarB_radical_charTwo CharTwo.two_eq_zero (g.val z)).mp hp
  have hs : a ^ 2 = 1 := by
    have h := ReflectionGeneration.isometry_preserves _ g z
    rw [ha, (formB n F).map_smul, formB_z] at h
    simpa only [smul_eq_mul, mul_one, pow_two] using h
  have hone : a = 1 := by
    rcases sq_eq_one_iff.mp hs with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  simpa only [hone, one_smul] using ha

theorem even_first (g : Theory.AlgebraicGroup.quadraticIsometrySubgroup (formB n F)) (x : VectorB n F) :
    (g.val x).1 = (g.val (x.1, 0)).1 := by
  have hx : x = (x.1, 0) + x.2 • z := by ext <;> simp [z]
  calc
    (g.val x).1 = (g.val ((x.1, 0) + x.2 • z)).1 := congrArg (fun t => (g.val t).1) hx
    _ = (g.val (x.1, 0)).1 := by rw [map_add, map_smul, even_fix_z]; simp [z]

def evenProjectionLinear (g : Theory.AlgebraicGroup.quadraticIsometrySubgroup (formB n F)) : VectorD n F ≃ₗ[F] VectorD n F where
  toFun x := (g.val (x, 0)).1
  invFun x := ((g⁻¹).val (x, 0)).1
  left_inv x := by
    dsimp only
    rw [← even_first (g⁻¹) (g.val (x, 0))]
    change (g.val.symm (g.val (x, 0))).1 = x
    rw [g.val.symm_apply_apply]
  right_inv x := by
    dsimp only
    rw [← even_first g ((g⁻¹).val (x, 0))]
    change (g.val (g.val.symm (x, 0))).1 = x
    rw [g.val.apply_symm_apply]
  map_add' x y := by
    simpa using
      congrArg Prod.fst (map_add g.val (x, 0) (y, 0))
  map_smul' a x := by
    simpa using
      congrArg Prod.fst (map_smul g.val a (x, 0))

theorem evenProjection_preserves (g : Theory.AlgebraicGroup.quadraticIsometrySubgroup (formB n F)) (x y : VectorD n F) :
    Matrix.PSp4Three.form (evenProjectionLinear g x) (evenProjectionLinear g y) =
      Matrix.PSp4Three.form x y := by
  have h := ClassicalOrthogonal.Quadratic.isometry_between_polar (formB n F) (formB n F) (ReflectionGeneration.isometryCarrierEquiv _ g) (x, 0) (y, 0)
  simp only [polarB_apply, CharTwo.two_eq_zero, zero_mul, add_zero, polarD_eq_symplectic] at h
  exact h

/-- Projection is a homomorphism into the existing primary symplectic matrix model. -/
def evenProjection : Theory.AlgebraicGroup.quadraticIsometrySubgroup (formB n F) →* Matrix.PSp4Three.Sp n F where
  toFun g := Matrix.PSp4Three.ofLinear (evenProjectionLinear g) (evenProjection_preserves g)
  map_one' := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Matrix.PSp4Three.Vector n F)
    intro x
    rw [Matrix.PSp4Three.ofLinear_apply, one_smul]
    rfl
  map_mul' g h := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Matrix.PSp4Three.Vector n F)
    intro x
    rw [mul_smul, Matrix.PSp4Three.ofLinear_apply, Matrix.PSp4Three.ofLinear_apply,
      Matrix.PSp4Three.ofLinear_apply]
    change (g.val (h.val (x, 0))).1 = (g.val ((h.val (x, 0)).1, 0)).1
    exact even_first g (h.val (x, 0))

@[simp] theorem evenProjection_apply (g : Theory.AlgebraicGroup.quadraticIsometrySubgroup (formB n F)) (x : VectorD n F) :
    evenProjection g • x = (g.val (x, 0)).1 :=
  Matrix.PSp4Three.ofLinear_apply (evenProjectionLinear g) (evenProjection_preserves g) x

theorem evenProjection_injective : Function.Injective (evenProjection (n := n) (F := F)) := by
  intro g h heq
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hfirst : (g.val x).1 = (h.val x).1 := by
    rw [even_first g, even_first h]
    simpa only [evenProjection_apply] using
      congrArg (fun k : Matrix.PSp4Three.Sp n F => k • x.1) heq
  apply Prod.ext hfirst
  have hqg := ReflectionGeneration.isometry_preserves _ g x
  have hqh := ReflectionGeneration.isometry_preserves _ h x
  rw [formB_apply, hfirst] at hqg
  rw [formB_apply] at hqh
  have hs : (g.val x).2 ^ 2 = (h.val x).2 ^ 2 := add_left_cancel (hqg.trans hqh.symm)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with ht | ht
  · exact ht
  · simpa only [CharTwo.neg_eq] using ht

variable [PerfectRing F 2]

def evenSingularLift (u : VectorD n F) : VectorB n F :=
  (u, (frobeniusEquiv F 2).symm (formD n F u))

theorem evenSingularLift_singular (u : VectorD n F) : formB n F (evenSingularLift u) = 0 := by
  rw [formB_apply]
  change formD n F u + ((frobeniusEquiv F 2).symm (formD n F u))^2 = 0
  have h : ((frobeniusEquiv F 2).symm (formD n F u))^2 = formD n F u :=
    (frobeniusEquiv F 2).apply_symm_apply _
  rw [h, CharTwo.add_self_eq_zero]

omit [PerfectRing F 2] in
theorem polarB_scalar_z (u : VectorB n F) (a : F) :
    (formB n F).polarBilin u (a • z) = 0 := by
  simp only [map_smul, polarB_apply, z, map_zero, CharTwo.two_eq_zero, zero_mul, add_zero, smul_zero]

theorem even_siegel_transvection (u : VectorD n F) (a : F) :
    evenProjection (siegelElement (formB n F) (evenSingularLift u) (a • z)
      (evenSingularLift_singular u) (polarB_scalar_z _ a)) = Matrix.PSp4Three.transvection u (a^2) := by
  apply Matrix.PSp4Three.ext_action
  intro x
  rw [evenProjection_apply, Matrix.PSp4Three.transvection_apply]
  change (ClassicalOrthogonal.Quadratic.siegel (formB n F) (evenSingularLift u) (a • z) (x, 0)).1 = _
  have hq : formB n F (a • z (n := n)) = a^2 := by
    rw [(formB n F).map_smul, formB_z]
    simp only [smul_eq_mul, mul_one, pow_two]
  have hp : (formB n F).polarBilin (x, 0) (evenSingularLift u) = Matrix.PSp4Three.form x u := by
    simp only [polarB_apply, CharTwo.two_eq_zero, zero_mul, add_zero, evenSingularLift,
      polarD_eq_symplectic]
  simp only [ClassicalOrthogonal.Quadratic.siegel, polarB_scalar_z, zero_smul, add_zero, hq, hp]
  change x - (Matrix.PSp4Three.form x u • (a • z (n := n))).1 -
    ((a^2 * Matrix.PSp4Three.form x u) • evenSingularLift u).1 = _
  simp only [z, evenSingularLift, Prod.smul_fst, smul_zero, sub_zero]
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, CharTwo.sub_eq_add]

theorem even_transvection_mem_image (u : VectorD n F) (a : F) :
    Matrix.PSp4Three.transvection u a ∈ (elementarySubgroup (formB n F)).map evenProjection := by
  let c := (frobeniusEquiv F 2).symm a
  have hc : c^2 = a := (frobeniusEquiv F 2).apply_symm_apply a
  refine ⟨siegelElement (formB n F) (evenSingularLift u) (c • z)
    (evenSingularLift_singular u) (polarB_scalar_z _ c), siegelElement_mem _ _ _ _ _, ?_⟩
  rw [even_siegel_transvection, hc]

/-- Every symplectic transvection has a preimage in the actual Omega subgroup. -/
theorem even_elementary_image :
    (elementarySubgroup (formB n F)).map evenProjection = ⊤ := by
  apply top_unique
  rw [← Matrix.PSp4Three.transvectionGroup_eq_top]
  change Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  rintro g ⟨u, a, rfl⟩
  exact even_transvection_mem_image u a

/-- Projection restricted to the elementary orthogonal carrier. -/
def oddOmegaProjection : OmegaOdd n F →* Matrix.PSp4Three.Sp n F :=
  evenProjection.comp (elementarySubgroup (formB n F)).subtype

theorem oddOmegaProjection_bijective : Function.Bijective (oddOmegaProjection (n := n) (F := F)) := by
  constructor
  · exact evenProjection_injective.comp Subtype.val_injective
  · intro g
    have hg : g ∈ (elementarySubgroup (formB n F)).map evenProjection := by
      rw [even_elementary_image]
      trivial
    obtain ⟨h, hh, he⟩ := hg
    exact ⟨⟨h, hh⟩, he⟩

/-- The actual elementary odd group and the full symplectic matrix group. -/
def oddOmegaEquivSp : OmegaOdd n F ≃* Matrix.PSp4Three.Sp n F :=
  MulEquiv.ofBijective oddOmegaProjection oddOmegaProjection_bijective

/-- The carrier equivalence acts by the literal projection on natural vectors. -/
@[simp] theorem oddOmegaEquivSp_apply (g : OmegaOdd n F) (x : VectorD n F) :
    oddOmegaEquivSp g • x = (g.val.val (x, 0)).1 := evenProjection_apply g.val x

omit [PerfectRing F 2] in
/-- The symplectic central quotient has no kernel in characteristic two. -/
theorem symplectic_center_eq_bot (hn : 0 < n) :
    Subgroup.center (Matrix.PSp4Three.Sp n F) = ⊥ := by
  apply bot_unique
  intro g hg
  obtain ⟨a, ha⟩ := Matrix.PSp4Three.central_is_scalar g hg
  have hs : a ^ 2 = 1 := by
    let i : Fin n := ⟨0, hn⟩
    have h := Matrix.PSp4Three.preserves g (Matrix.PSp4Three.e i) (Matrix.PSp4Three.f i)
    rw [← Matrix.PSp4Three.smul_eq_mulVec, ← Matrix.PSp4Three.smul_eq_mulVec, ha, ha] at h
    simpa [map_smul, Matrix.PSp4Three.e, Matrix.PSp4Three.form_f_right, pow_two] using h
  have hone : a = 1 := by
    rcases sq_eq_one_iff.mp hs with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  rw [Subgroup.mem_bot]
  apply Matrix.PSp4Three.ext_action
  intro x
  rw [ha, hone, one_smul, one_smul]

/-- The specified projective Omega carrier is actually the projective symplectic group. -/
def oddProjectiveEquivPSp (hn : 0 < n) : POmegaOdd n F ≃* Matrix.PSp4Three.PSp n F :=
  (elementaryProjectiveEquiv (formB n F)).symm.trans
      (oddOmegaEquivSp.trans (MulEquiv.ofBijective Matrix.PSp4Three.projection
        ⟨by
          apply (MonoidHom.ker_eq_bot_iff _).mp
          rw [Matrix.PSp4Three.projection_kernel, symplectic_center_eq_bot hn],
          Matrix.PSp4Three.projection_surjective⟩))

/-- Compatibility with the two actual projective quotient maps. -/
@[simp] theorem oddProjectiveEquivPSp_apply (hn : 0 < n) (g : OmegaOdd n F) :
    oddProjectiveEquivPSp hn (projectiveElementaryMap (formB n F) g) =
      Matrix.PSp4Three.projection (evenProjection g.val) := by
  change Matrix.PSp4Three.projection (oddOmegaEquivSp
    ((elementaryProjectiveEquiv (formB n F)).symm
      (elementaryProjectiveEquiv (formB n F) g))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

end ClassicalOrthogonal.TheoremDRootNormalizer
