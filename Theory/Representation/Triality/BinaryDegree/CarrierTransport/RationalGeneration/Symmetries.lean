module

public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.RationalGeneration.Coordinates
import Mathlib.Tactic

/-!
# Even rational symmetry words are rational root words

The coordinate swap in e₀ + f₀ permutes the root groups without changing their
parameters. Over a finite characteristic-two coefficient field, squaring is
bijective. Rational coordinate elimination therefore conjugates each rational
anisotropic symmetry to this swap using rational roots. Pairs, and hence all
even symmetry words, lie in the rational root closure.

This refines `EvenOrthogonalElementaryGeneration.Symmetries`, using the same
coordinate identities. Sources: GLS3, §§1.10–1.12 and §2.7.
-/

@[expose] public section
noncomputable section
namespace Theory.AlgebraicGroup.RationalOrthogonal
open EvenOrthogonalElementary
variable {k : Type*} [Field k]
variable (F : Subfield k)

private lemma symmetry_sq (a : AnisotropicVector (hyperbolicForm (k := k) 4)) :
    symmetryPoint a * symmetryPoint a = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  exact conjugationSymmetry_involutive _ a.1 a.2 v

private lemma conjugate_upper_mem [CharP k 2] (i j : Fin 4) (hij : i ≠ j) {a : k} (ha : a ∈ F) :
    standardSymmetry * hyperbolicUpperRootPoint 4 i j hij a * standardSymmetry ∈
      rootSubgroup F := by
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
    exact lower_mem F _ _ _ ha
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
      exact skewUpper_mem F _ _ _ ha
    · have heq : standardSymmetry * hyperbolicUpperRootPoint 4 i j hij a * standardSymmetry =
          hyperbolicUpperRootPoint 4 i j hij a := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro v
        simp only [point_mul_apply, standardSymmetry_apply, upper_apply]
        apply Prod.ext <;> funext p <;> by_cases hp : p = 0 <;>
          simp [hp, hi, Ne.symm hi, hj, Ne.symm hj]
      rw [heq]
      exact upper_mem F _ _ _ ha

private lemma conjugate_lower_mem [CharP k 2] (i j : Fin 4) (hij : i ≠ j) {a : k} (ha : a ∈ F) :
    standardSymmetry * hyperbolicLowerRootPoint 4 i j hij a * standardSymmetry ∈
      rootSubgroup F := by
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
    exact upper_mem F _ _ _ ha
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
      exact upper_mem F _ _ _ ha
    · have heq : standardSymmetry * hyperbolicLowerRootPoint 4 i j hij a * standardSymmetry =
          hyperbolicLowerRootPoint 4 i j hij a := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro v
        simp only [point_mul_apply, standardSymmetry_apply, lower_apply]
        apply Prod.ext <;> funext p <;> by_cases hp : p = 0 <;>
          simp [hp, hi, Ne.symm hi, hj, Ne.symm hj]
      rw [heq]
      exact lower_mem F _ _ _ ha

private lemma conjugate_skewUpper_mem [CharP k 2] (i j : Fin 4) (hij : i ≠ j) {a : k} (ha : a ∈ F) :
    standardSymmetry * hyperbolicSkewUpperRootPoint 4 i j hij a * standardSymmetry ∈
      rootSubgroup F := by
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
    exact upper_mem F _ _ _ ha
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
      exact upper_mem F _ _ _ ha
    · have heq : standardSymmetry * hyperbolicSkewUpperRootPoint 4 i j hij a * standardSymmetry =
          hyperbolicSkewUpperRootPoint 4 i j hij a := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro v
        simp only [point_mul_apply, standardSymmetry_apply, skewUpper_apply]
        apply Prod.ext <;> funext p <;> by_cases hp : p = 0 <;>
          simp [hp, hi, Ne.symm hi, hj, Ne.symm hj]
      rw [heq]
      exact skewUpper_mem F _ _ _ ha

/-- The first coordinate symmetry normalizes the root-matrix subgroup. -/
public lemma standardSymmetry_conjugate_mem [CharP k 2]
    {g : quadraticIsometrySubgroup (hyperbolicForm (k := k) 4)}
    (hg : g ∈ rootSubgroup F) :
    standardSymmetry * g * standardSymmetry ∈ rootSubgroup F := by
  have hle : rootSubgroup (k := k) F ≤
      (rootSubgroup F).comap
        (MulAut.conj standardSymmetry).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨r, a⟩, rfl⟩
    change standardSymmetry * evenOrthogonalRootQuadraticPoint 4 r (a : k) *
      standardSymmetry⁻¹ ∈ rootSubgroup F
    rw [standardSymmetry_inv]
    rcases r with ⟨⟨⟨i, j⟩, hij⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
    rcases hs with hs | hs <;> rcases ht with ht | ht <;>
      subst s <;> subst t <;>
      norm_num only [evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
        reduceDIte]
    · exact conjugate_lower_mem F i j hij.ne a.property
    · exact conjugate_upper_mem F j i hij.ne' a.property
    · exact conjugate_upper_mem F i j hij.ne a.property
    · exact conjugate_skewUpper_mem F i j hij.ne a.property
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


/-- Squaring is bijective on a finite coefficient field in characteristic two. -/
theorem exists_sqrt [CharP k 2] [Finite F] {a : k} (ha : a ∈ F) :
    ∃ c : k, c ∈ F ∧ a = c * c := by
  obtain ⟨c, hc⟩ := (Finite.injective_iff_surjective.mp (frobenius_inj F 2)) ⟨a, ha⟩
  refine ⟨c, c.property, ?_⟩
  have h := congrArg Subtype.val hc
  simpa only [frobenius_def, pow_two, Subfield.coe_mul] using h.symm

/-- The quadratic norm of a rational vector belongs to its coefficient field. -/
theorem norm_mem {v : HyperbolicSpace k 4} (hv : HasCoordinates F v) :
    hyperbolicForm 4 v ∈ F := by
  rw [hyperbolicForm_apply]
  exact F.sum_mem fun i _ => F.mul_mem (hv.1 i) (hv.2 i)

variable [IsAlgClosed k] [CharP k 2] [Finite F]

/-- Normalization and elimination of a rational symmetry use only rational roots. -/
theorem exists_symmetry_conjugate
    (a : AnisotropicVector (hyperbolicForm (k := k) 4)) (ha : HasCoordinates F a.1) :
    ∃ g : quadraticIsometrySubgroup (hyperbolicForm (k := k) 4),
      g ∈ rootSubgroup F ∧ symmetryPoint a = g⁻¹ * standardSymmetry * g := by
  obtain ⟨c, hcF, hc⟩ := exists_sqrt F (F.inv_mem (norm_mem F ha))
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
  have hbr : HasCoordinates F b.1 :=
    ⟨fun i => F.mul_mem hcF (ha.1 i), fun i => F.mul_mem hcF (ha.2 i)⟩
  obtain ⟨g, hg, hgb⟩ := exists_map_norm_one F b.1 hbr hb
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

/-- Two rational anisotropic symmetries form a word in rational root matrices. -/
theorem symmetryPair_mem
    (a b : AnisotropicVector (hyperbolicForm (k := k) 4))
    (ha : HasCoordinates F a.1) (hb : HasCoordinates F b.1) :
    symmetryPoint a * symmetryPoint b ∈ rootSubgroup F := by
  have hmem (c : AnisotropicVector (hyperbolicForm (k := k) 4))
      (hc : HasCoordinates F c.1) :
      symmetryPoint c * standardSymmetry ∈ rootSubgroup F := by
    obtain ⟨g, hg, heq⟩ := exists_symmetry_conjugate F c hc
    rw [heq, mul_assoc, mul_assoc]
    exact mul_mem (inv_mem hg) (standardSymmetry_conjugate_mem F hg)
  have heq : symmetryPoint a * symmetryPoint b =
      (symmetryPoint a * standardSymmetry) * (symmetryPoint b * standardSymmetry)⁻¹ := by
    rw [mul_inv_rev, standardSymmetry_inv]
    have hb' : (symmetryPoint b)⁻¹ = symmetryPoint b :=
      (eq_inv_iff_mul_eq_one.mpr (symmetry_sq b)).symm
    rw [hb']
    calc
      symmetryPoint a * symmetryPoint b =
          symmetryPoint a * (standardSymmetry * standardSymmetry) * symmetryPoint b := by
            rw [standardSymmetry_sq, mul_one]
      _ = _ := by group
  rw [heq]
  exact mul_mem (hmem a ha) (inv_mem (hmem b hb))

/-- Every even word of rational symmetries lies in the rational root closure. -/
theorem even_symmetryProduct_mem
    (as : List (AnisotropicVector (hyperbolicForm (k := k) 4)))
    (hr : ∀ a ∈ as, HasCoordinates F a.1) (he : Even as.length) :
    symmetryProductPoint as ∈ rootSubgroup F := by
  induction as using List.twoStepInduction with
  | nil => simp
  | singleton a => simp at he
  | cons_cons a b as ih =>
      have he' : Even as.length := by
        obtain ⟨n, hn⟩ := he
        refine ⟨n - 1, ?_⟩
        simp only [List.length_cons] at hn
        omega
      rw [symmetryProductPoint_cons, symmetryProductPoint_cons, ← mul_assoc]
      exact mul_mem (symmetryPair_mem F a b (hr a (by simp)) (hr b (by simp)))
        (ih (fun c hc => hr c (by simp [hc])) he')

end Theory.AlgebraicGroup.RationalOrthogonal
