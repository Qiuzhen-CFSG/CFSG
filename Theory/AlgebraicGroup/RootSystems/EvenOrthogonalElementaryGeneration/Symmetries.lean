module

public import Theory.AlgebraicGroup.RootSystems.EvenOrthogonalElementaryGeneration.Coordinates
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenSpinDerivedRange
import Mathlib.Tactic

/-!
# A coordinate symmetry and the elementary orthogonal subgroup

In characteristic two, symmetry in `e₀ + f₀` swaps the first hyperbolic
coordinates. This symmetry permutes the coordinate root groups, so it
normalizes their generated subgroup. Coordinate elimination and square roots
then express any anisotropic symmetry as an elementary conjugate of this one.
This is the concrete orthogonal generation argument underlying GLS3,
Sections 1.10--1.12.
-/

universe u
namespace Theory.AlgebraicGroup.EvenOrthogonalElementary
variable {k : Type u} [Field k]

/-- The first standard anisotropic vector, of quadratic norm one. -/
@[expose] public noncomputable def standardVector :
    AnisotropicVector (hyperbolicForm (k := k) 4) :=
  ⟨(Pi.single 0 1, Pi.single 0 1), by simp [hyperbolicForm_apply, Pi.single_apply]⟩

/-- The conjugation symmetry in the first standard anisotropic vector. -/
@[expose] public noncomputable def standardSymmetry :
    quadraticIsometrySubgroup (hyperbolicForm (k := k) 4) :=
  symmetryPoint standardVector

private lemma symmetry_sq (a : AnisotropicVector (hyperbolicForm (k := k) 4)) :
    symmetryPoint a * symmetryPoint a = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  exact conjugationSymmetry_involutive _ a.1 a.2 v

public lemma standardSymmetry_sq :
    standardSymmetry (k := k) * standardSymmetry = 1 := symmetry_sq _

public lemma standardSymmetry_inv :
    (standardSymmetry (k := k))⁻¹ = standardSymmetry :=
  (eq_inv_iff_mul_eq_one.mpr standardSymmetry_sq).symm

public lemma standardSymmetry_apply [CharP k 2] (v : HyperbolicSpace k 4) :
    (standardSymmetry (k := k)).1 v =
      (fun i => if i = 0 then v.2 0 else v.1 i,
       fun i => if i = 0 then v.1 0 else v.2 i) := by
  rw [standardSymmetry, symmetryPoint_apply, conjugationSymmetry_apply]
  rw [← QuadraticMap.polarBilin_apply_apply, hyperbolicForm_polar]
  apply Prod.ext <;> funext i <;> by_cases hi : i = 0 <;>
    simp [standardVector, hyperbolicForm_apply, Finset.sum_add_distrib,
      Pi.single_apply, hi, CharTwo.sub_eq_add, CharTwo.add_self_eq_zero,
      add_assoc, add_left_comm]

private lemma conjugate_upper_mem [CharP k 2] (i j : Fin 4) (hij : i ≠ j) (a : k) :
    standardSymmetry * hyperbolicUpperRootPoint 4 i j hij a * standardSymmetry ∈
      evenOrthogonalElementarySubgroup 4 := by
  by_cases hi : i = 0
  · subst i
    have heq : standardSymmetry * hyperbolicUpperRootPoint 4 0 j hij a * standardSymmetry =
        hyperbolicLowerRootPoint 4 0 j hij a := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      simp only [point_mul_apply, standardSymmetry_apply, upper_apply, lower_apply]
      apply Prod.ext <;> funext p <;> by_cases hp : p = 0 <;> by_cases hpj : p = j <;>
        simp [hp, hpj, hij, hij.symm, CharTwo.sub_eq_add]
    rw [heq]
    exact lower_mem _ _ _ _ _
  · by_cases hj : j = 0
    · subst j
      have heq : standardSymmetry * hyperbolicUpperRootPoint 4 i 0 hij a * standardSymmetry =
          hyperbolicSkewUpperRootPoint 4 i 0 hij a := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro v
        simp only [point_mul_apply, standardSymmetry_apply, upper_apply, skewUpper_apply]
        apply Prod.ext <;> funext p <;> by_cases hp : p = 0 <;> by_cases hpi : p = i <;>
          simp [hp, hpi, hi, Ne.symm hi, CharTwo.sub_eq_add]
      rw [heq]
      exact skewUpper_mem _ _ _ _ _
    · have heq : standardSymmetry * hyperbolicUpperRootPoint 4 i j hij a * standardSymmetry =
          hyperbolicUpperRootPoint 4 i j hij a := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro v
        simp only [point_mul_apply, standardSymmetry_apply, upper_apply]
        apply Prod.ext <;> funext p <;> by_cases hp : p = 0 <;>
          simp [hp, hi, Ne.symm hi, hj, Ne.symm hj]
      rw [heq]
      exact upper_mem _ _ _ _ _

private lemma conjugate_lower_mem [CharP k 2] (i j : Fin 4) (hij : i ≠ j) (a : k) :
    standardSymmetry * hyperbolicLowerRootPoint 4 i j hij a * standardSymmetry ∈
      evenOrthogonalElementarySubgroup 4 := by
  by_cases hi : i = 0
  · subst i
    have heq : standardSymmetry * hyperbolicLowerRootPoint 4 0 j hij a * standardSymmetry =
        hyperbolicUpperRootPoint 4 0 j hij a := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      simp only [point_mul_apply, standardSymmetry_apply, upper_apply, lower_apply]
      apply Prod.ext <;> funext p <;> by_cases hp : p = 0 <;> by_cases hpj : p = j <;>
        simp [hp, hpj, hij, hij.symm, CharTwo.sub_eq_add]
    rw [heq]
    exact upper_mem _ _ _ _ _
  · by_cases hj : j = 0
    · subst j
      have heq : standardSymmetry * hyperbolicLowerRootPoint 4 i 0 hij a * standardSymmetry =
          hyperbolicUpperRootPoint 4 0 i hij.symm a := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro v
        simp only [point_mul_apply, standardSymmetry_apply, upper_apply, lower_apply]
        apply Prod.ext <;> funext p <;> by_cases hp : p = 0 <;> by_cases hpi : p = i <;>
          simp [hp, hpi, hi, Ne.symm hi, CharTwo.sub_eq_add]
      rw [heq]
      exact upper_mem _ _ _ _ _
    · have heq : standardSymmetry * hyperbolicLowerRootPoint 4 i j hij a * standardSymmetry =
          hyperbolicLowerRootPoint 4 i j hij a := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro v
        simp only [point_mul_apply, standardSymmetry_apply, lower_apply]
        apply Prod.ext <;> funext p <;> by_cases hp : p = 0 <;>
          simp [hp, hi, Ne.symm hi, hj, Ne.symm hj]
      rw [heq]
      exact lower_mem _ _ _ _ _

private lemma conjugate_skewUpper_mem [CharP k 2] (i j : Fin 4) (hij : i ≠ j) (a : k) :
    standardSymmetry * hyperbolicSkewUpperRootPoint 4 i j hij a * standardSymmetry ∈
      evenOrthogonalElementarySubgroup 4 := by
  by_cases hi : i = 0
  · subst i
    have heq : standardSymmetry * hyperbolicSkewUpperRootPoint 4 0 j hij a * standardSymmetry =
        hyperbolicUpperRootPoint 4 j 0 hij.symm a := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      simp only [point_mul_apply, standardSymmetry_apply, upper_apply, skewUpper_apply]
      apply Prod.ext <;> funext p <;> by_cases hp : p = 0 <;> by_cases hpj : p = j <;>
        simp [hp, hpj, hij, hij.symm, CharTwo.sub_eq_add]
    rw [heq]
    exact upper_mem _ _ _ _ _
  · by_cases hj : j = 0
    · subst j
      have heq : standardSymmetry * hyperbolicSkewUpperRootPoint 4 i 0 hij a * standardSymmetry =
          hyperbolicUpperRootPoint 4 i 0 hij a := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro v
        simp only [point_mul_apply, standardSymmetry_apply, upper_apply, skewUpper_apply]
        apply Prod.ext <;> funext p <;> by_cases hp : p = 0 <;> by_cases hpi : p = i <;>
          simp [hp, hpi, hi, Ne.symm hi, CharTwo.sub_eq_add]
      rw [heq]
      exact upper_mem _ _ _ _ _
    · have heq : standardSymmetry * hyperbolicSkewUpperRootPoint 4 i j hij a * standardSymmetry =
          hyperbolicSkewUpperRootPoint 4 i j hij a := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro v
        simp only [point_mul_apply, standardSymmetry_apply, skewUpper_apply]
        apply Prod.ext <;> funext p <;> by_cases hp : p = 0 <;>
          simp [hp, hi, Ne.symm hi, hj, Ne.symm hj]
      rw [heq]
      exact skewUpper_mem _ _ _ _ _

/-- The first coordinate symmetry normalizes the root-matrix subgroup. -/
public lemma standardSymmetry_conjugate_mem [CharP k 2]
    {g : quadraticIsometrySubgroup (hyperbolicForm (k := k) 4)}
    (hg : g ∈ evenOrthogonalElementarySubgroup 4) :
    standardSymmetry * g * standardSymmetry ∈ evenOrthogonalElementarySubgroup 4 := by
  have hle : evenOrthogonalElementarySubgroup (k := k) 4 ≤
      (evenOrthogonalElementarySubgroup 4).comap
        (MulAut.conj standardSymmetry).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨r, a⟩, rfl⟩
    change standardSymmetry * evenOrthogonalRootQuadraticPoint 4 r a *
      standardSymmetry⁻¹ ∈ evenOrthogonalElementarySubgroup 4
    rw [standardSymmetry_inv]
    rcases r with ⟨⟨⟨i, j⟩, hij⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
    rcases hs with hs | hs <;> rcases ht with ht | ht <;>
      subst s <;> subst t <;>
      norm_num only [evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
        reduceDIte]
    · exact conjugate_lower_mem i j hij.ne a
    · exact conjugate_upper_mem j i hij.ne' a
    · exact conjugate_upper_mem i j hij.ne a
    · exact conjugate_skewUpper_mem i j hij.ne a
  simpa only [Subgroup.mem_comap, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulAut.conj_apply, standardSymmetry_inv] using hle hg


private lemma symmetry_smul (a : AnisotropicVector (hyperbolicForm (k := k) 4))
    (c : k) (hc : c ≠ 0) :
    symmetryPoint (⟨c • a.1, by
      rw [QuadraticMap.map_smul]
      exact mul_ne_zero (mul_ne_zero hc hc) a.2⟩ :
      AnisotropicVector (hyperbolicForm (k := k) 4)) = symmetryPoint a := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  simp only [symmetryPoint_apply, conjugationSymmetry_apply,
    QuadraticMap.map_smul, QuadraticMap.polar_smul_left, smul_smul, smul_eq_mul]
  apply congrArg (fun t : k => t • a.1 - v)
  field_simp [hc, a.2]

private lemma symmetry_conjugate
    (g : quadraticIsometrySubgroup (hyperbolicForm (k := k) 4))
    (a : AnisotropicVector (hyperbolicForm (k := k) 4)) :
    symmetryPoint (⟨g.1 a.1, by
      rw [(mem_quadraticIsometrySubgroup _ _).1 g.2]
      exact a.2⟩ : AnisotropicVector (hyperbolicForm (k := k) 4)) =
      g * symmetryPoint a * g⁻¹ := by
  have hQ (x : HyperbolicSpace k 4) : hyperbolicForm 4 (g.1 x) = hyperbolicForm 4 x :=
    (mem_quadraticIsometrySubgroup _ _).1 g.2 x
  have hpolar (x y : HyperbolicSpace k 4) :
      QuadraticMap.polar (hyperbolicForm 4) (g.1 x) (g.1 y) =
      QuadraticMap.polar (hyperbolicForm 4) x y := by
    simp only [QuadraticMap.polar, ← map_add, hQ]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change conjugationSymmetry _ (g.1 a.1) _ v =
    g.1 (conjugationSymmetry _ a.1 a.2 ((g⁻¹).1 v))
  rw [conjugationSymmetry_apply, conjugationSymmetry_apply, map_sub, map_smul, hQ]
  have hcancel : g.1 ((g⁻¹).1 v) = v := LinearEquiv.apply_symm_apply g.1 v
  have hp := hpolar a.1 ((g⁻¹).1 v)
  rw [hcancel] at hp
  rw [hp, hcancel]

/-- Every anisotropic symmetry is an elementary conjugate of the first
coordinate symmetry. Algebraic closure is used only to normalize its vector. -/
public theorem exists_symmetry_conjugate [IsAlgClosed k]
    (a : AnisotropicVector (hyperbolicForm (k := k) 4)) :
    ∃ g : quadraticIsometrySubgroup (hyperbolicForm (k := k) 4),
      g ∈ evenOrthogonalElementarySubgroup 4 ∧
      symmetryPoint a = g⁻¹ * standardSymmetry * g := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_eq_mul_self (hyperbolicForm 4 a.1)⁻¹
  have hc0 : c ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hc
    exact inv_ne_zero a.2 hc
  let b : AnisotropicVector (hyperbolicForm (k := k) 4) :=
    ⟨c • a.1, by
      rw [QuadraticMap.map_smul]
      exact mul_ne_zero (mul_ne_zero hc0 hc0) a.2⟩
  have hb : hyperbolicForm 4 b.1 = 1 := by
    change hyperbolicForm 4 (c • a.1) = 1
    rw [QuadraticMap.map_smul, smul_eq_mul, ← hc, inv_mul_cancel₀ a.2]
  obtain ⟨g, hg, hgb⟩ := exists_map_norm_one b.1 hb
  have hconj := symmetry_conjugate g b
  have hb' : symmetryPoint b = symmetryPoint a := symmetry_smul a c hc0
  have himage :
      (⟨g.1 b.1, by
        rw [(mem_quadraticIsometrySubgroup _ _).1 g.2]
        exact b.2⟩ : AnisotropicVector (hyperbolicForm (k := k) 4)) =
      standardVector := Subtype.ext hgb
  rw [himage, hb'] at hconj
  refine ⟨g, hg, ?_⟩
  change symmetryPoint a = g⁻¹ * symmetryPoint standardVector * g
  rw [hconj]
  group

/-- A pair of anisotropic symmetries is a product of coordinate root matrices. -/
public theorem symmetryPair_mem [IsAlgClosed k] [CharP k 2]
    (a b : AnisotropicVector (hyperbolicForm (k := k) 4)) :
    symmetryPoint a * symmetryPoint b ∈ evenOrthogonalElementarySubgroup 4 := by
  have hmem (c : AnisotropicVector (hyperbolicForm (k := k) 4)) :
      symmetryPoint c * standardSymmetry ∈ evenOrthogonalElementarySubgroup 4 := by
    obtain ⟨g, hg, heq⟩ := exists_symmetry_conjugate c
    rw [heq, mul_assoc, mul_assoc]
    exact mul_mem (inv_mem hg) (standardSymmetry_conjugate_mem hg)
  have heq : symmetryPoint a * symmetryPoint b =
      (symmetryPoint a * standardSymmetry) * (symmetryPoint b * standardSymmetry)⁻¹ := by
    rw [mul_inv_rev, standardSymmetry_inv]
    have hb : (symmetryPoint b)⁻¹ = symmetryPoint b :=
      (eq_inv_iff_mul_eq_one.mpr (symmetry_sq b)).symm
    rw [hb]
    calc
      symmetryPoint a * symmetryPoint b =
          symmetryPoint a * (standardSymmetry * standardSymmetry) * symmetryPoint b := by
            rw [standardSymmetry_sq, mul_one]
      _ = _ := by group
  rw [heq]
  exact mul_mem (hmem a) (inv_mem (hmem b))

end Theory.AlgebraicGroup.EvenOrthogonalElementary
