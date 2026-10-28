module

public import Theory.AlgebraicGroup.Bor1.FlagCurve.ChartFactorization
public import Theory.AlgebraicGroup.Variety.OpenSubvariety

/-!
# Native projective-line coordinates

The two native affine charts are precisely the polynomial curves with vectors
(1,t) and (t,1). Their rational overlap parameters are nonzero reciprocals.
These identities supply the chart gluing step for the monomial-curve proof of
Borel, Linear Algebraic Groups, §13.13.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped LinearAlgebra.Projectivization
open Theory.AlgebraicGroup.Variety.Geometric
open Theory.AlgebraicGroup.Variety.Geometric.ProjectivePolynomialCurve
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u
variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency false in
theorem affinePoint_surjective : Function.Surjective (affinePoint (k := k)) := by
  intro p
  let φ : CommRingCat.of (Polynomial k) ⟶ CommRingCat.of k := Spec.preimage p.1
  have hC : CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k) ≫ φ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, show Spec.map φ = p.1 from Spec.map_preimage p.1, Spec.map_id]
    exact p.2
  have hφ : φ.hom = Polynomial.evalRingHom (φ.hom Polynomial.X) := by
    apply Polynomial.ringHom_ext
    · intro r
      simpa using congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of k => f.hom r) hC
    · simp
  refine ⟨φ.hom Polynomial.X, ?_⟩
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom _)) = p.1
  rw [← hφ]
  exact Spec.map_preimage p.1

set_option backward.isDefEq.respectTransparency false in
theorem projectiveLineChartInclusion_eq_curve (i : Fin 2) :
    projectiveLineChartInclusion (k := k) i =
      curve (fun j : Fin 2 => if j = i then 1 else Polynomial.X)
        ⟨i, by simp⟩ := by
  apply Morphism.ext
  rw [← polynomialChartFactor_fac _ i (by simp), polynomialChartFactor_eq]
  change Spec.map (CommRingCat.ofHom (chartToPolynomial (k := k) i)) ≫
      ((Proj.basicOpenIsoSpec _ _ _ _).inv ≫ _) = _
  rw [← Category.assoc]
  rfl

variable [IsAlgClosed k]

theorem projectiveLineChartInclusion_point (i : Fin 2) (a : k) :
    projectiveLineChartInclusion (k := k) i (affinePoint a) =
      projectivePointOfVector (fun j : Fin 2 => if j = i then 1 else a)
        (by intro h; have := congr_fun h i; simp at this) := by
  rw [projectiveLineChartInclusion_eq_curve, curve_point]
  congr 1
  funext j
  by_cases hj : j = i <;> simp [hj]

theorem projectiveLineChart_coordinates_inverse
    (a b : k)
    (h : projectiveLineChartInclusion (k := k) 0 (affinePoint a) =
      projectiveLineChartInclusion (k := k) 1 (affinePoint b)) :
    a ≠ 0 ∧ b = a⁻¹ := by
  rw [projectiveLineChartInclusion_point, projectiveLineChartInclusion_point] at h
  have hp := (projectivePointOfVector_eq_iff_mk_eq _ _ _ _).mp h
  obtain ⟨r, hr⟩ := (Projectivization.mk_eq_mk_iff' k _ _ _ _).mp hp
  have h0 := congr_fun hr 0
  have h1 := congr_fun hr 1
  change r * b = 1 at h0
  change r * 1 = a at h1
  rw [mul_one] at h1
  have hane : a ≠ 0 := by
    intro ha
    rw [h1, ha, zero_mul] at h0
    exact zero_ne_one h0
  refine ⟨hane, ?_⟩
  rw [h1] at h0
  calc b = a⁻¹ * (a * b) := by rw [← mul_assoc, inv_mul_cancel₀ hane, one_mul]
       _ = a⁻¹ := by rw [h0, mul_one]

end Theory.AlgebraicGroup.Bor1.FlagCurve
