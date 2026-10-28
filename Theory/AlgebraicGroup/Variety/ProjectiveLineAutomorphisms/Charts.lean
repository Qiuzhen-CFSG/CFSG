module

public import Theory.AlgebraicGroup.Variety.ProjectiveLineAutomorphisms.Affine
public import Theory.AlgebraicGroup.Instance.PGL2ProjectiveAction

import all Theory.AlgebraicGroup.Instance.PGL2ProjectiveAction

/-!
# Rational points in the actual projective-line charts

The Spec evaluation at t, followed by either projective chart inclusion, is
the normalized homogeneous point. The proof reads a homogeneous linear
equation through Proj localization; it therefore identifies the actual scheme
point rather than introducing a replacement chart parametrization. This is
the coordinate bridge used in Borel 10.8.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped LinearAlgebra.Projectivization
namespace Theory.AlgebraicGroup.Variety.Geometric.ProjectiveLineAutomorphisms
noncomputable section
universe u
variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency false in
private theorem away_image_mem (i : Fin 2)
    (x : Spec (.of (HomogeneousLocalization.Away (p1Grading (k := k)) (MvPolynomial.X i))))
    (n : ℕ) (p : MvPolynomial (Fin 2) k) (hp : p ∈ p1Grading (k := k) n) :
    p ∈ ((Proj.awayι (p1Grading (k := k)) (MvPolynomial.X i)
      (coordinate_mem_p1Grading i) Nat.zero_lt_one) x).asHomogeneousIdeal ↔
      HomogeneousLocalization.Away.mk (p1Grading (k := k))
        (coordinate_mem_p1Grading i) n p (by simpa using hp) ∈ x.asIdeal := by
  let E := Proj.basicOpenIsoSpec (p1Grading (k := k)) (MvPolynomial.X i)
    (coordinate_mem_p1Grading i) Nat.zero_lt_one
  let y := E.inv x
  let z : HomogeneousLocalization.NumDenSameDeg (p1Grading (k := k))
      (Submonoid.powers (MvPolynomial.X i)) :=
    { deg := n
      num := ⟨p,hp⟩
      den := ⟨MvPolynomial.X i ^ n,MvPolynomial.isHomogeneous_X_pow _ _⟩
      den_mem := ⟨n,rfl⟩ }
  have hy : (ProjectiveSpectrum.Proj.toSpec (p1Grading (k := k))
      (MvPolynomial.X i)).base y = x := by
    change E.hom (E.inv x) = x
    exact congrArg (fun f => f x) E.inv_hom_id
  have hz : HomogeneousLocalization.mk z =
      HomogeneousLocalization.Away.mk (p1Grading (k := k))
        (coordinate_mem_p1Grading i) n p (by simpa using hp) := by
    apply HomogeneousLocalization.val_injective
    rfl
  have hh := (ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply (p1Grading (k := k)) y z).symm
  rw [hy,hz] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
theorem chartPoint_homogeneous_mem (i : Fin 2) (t : k)
    (n : ℕ) (p : MvPolynomial (Fin 2) k) (hp : p ∈ p1Grading (k := k) n) :
    p ∈ (((projectiveLineChartInclusion (k := k) i) (affinePoint t)).val
        (IsLocalRing.closedPoint k)).asHomogeneousIdeal ↔
      (dehomogenize (k := k) i p).eval t = 0 := by
  change p ∈ ((Proj.awayι (p1Grading (k := k)) (MvPolynomial.X i)
      (coordinate_mem_p1Grading i) Nat.zero_lt_one)
    ((Spec.map (CommRingCat.ofHom (chartToPolynomial (k := k) i)))
      ((Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom t)))
        (IsLocalRing.closedPoint k)))).asHomogeneousIdeal ↔ _
  rw [away_image_mem i _ n p hp]
  change chartToPolynomial (k := k) i
    (HomogeneousLocalization.Away.mk (p1Grading (k := k))
      (coordinate_mem_p1Grading i) n p (by simpa using hp)) ∈
        (PrimeSpectrum.comap (Polynomial.evalRingHom t) (IsLocalRing.closedPoint k)).asIdeal ↔ _
  rw [PrimeSpectrum.comap_asIdeal,Ideal.mem_comap]
  have hbot : (IsLocalRing.closedPoint k).asIdeal = (⊥ : Ideal k) :=
    (Ideal.eq_bot_or_top _).resolve_right (IsLocalRing.closedPoint k).isPrime.ne_top
  rw [hbot,Ideal.mem_bot]
  have he : chartToPolynomial (k := k) i
      (HomogeneousLocalization.Away.mk (p1Grading (k := k))
        (coordinate_mem_p1Grading i) n p (by simpa using hp)) = dehomogenize (k := k) i p := by
    rw [show chartToPolynomial (k := k) i
      (HomogeneousLocalization.Away.mk (p1Grading (k := k))
        (coordinate_mem_p1Grading i) n p (by simpa using hp)) = dehomogenize (k := k) i p * 1 ^ n by
      apply Localization.awayLift_mk
      simp]
    simp
  rw [he,Polynomial.coe_evalRingHom]

def chartVector (i : Fin 2) (t : k) : Fin 2 → k := fun j => if j=i then 1 else t

theorem chartVector_ne_zero (i : Fin 2) (t : k) : chartVector i t ≠ 0 := by
  intro he
  have hi := congrFun he i
  simp [chartVector] at hi

variable [IsAlgClosed k]

theorem point_vector_exists (x : Point (projectiveLine k)) :
    ∃ (v : Fin 2 → k) (hv : v ≠ 0), x = projectivePointOfVector v hv := by
  induction h : projectiveLinePointEquiv x using Projectivization.ind with
  | h v hv =>
    refine ⟨v,hv,?_⟩
    apply projectiveLinePointEquiv.injective
    simpa only [projectiveLinePointEquiv_projectivePointOfVector] using h

set_option backward.isDefEq.respectTransparency false in
/-- Literal evaluation in either affine chart gives the normalized homogeneous point. -/
theorem chartInclusion_affinePoint (i : Fin 2) (t : k) :
    (projectiveLineChartInclusion (k := k) i) (affinePoint t) =
      projectivePointOfVector (chartVector i t) (chartVector_ne_zero i t) := by
  let p : MvPolynomial (Fin 2) k := MvPolynomial.X (other i) - t • MvPolynomial.X i
  have hp : p ∈ p1Grading (k := k) 1 :=
    (p1Grading (k := k) 1).sub_mem (coordinate_mem_p1Grading (other i))
      ((p1Grading (k := k) 1).smul_mem t (coordinate_mem_p1Grading i))
  have hm : p ∈ (((projectiveLineChartInclusion (k := k) i) (affinePoint t)).val
      (IsLocalRing.closedPoint k)).asHomogeneousIdeal := by
    rw [chartPoint_homogeneous_mem i t 1 p hp]
    simp [p]
  obtain ⟨v,hv,he⟩ := point_vector_exists ((projectiveLineChartInclusion (k := k) i) (affinePoint t))
  rw [he] at hm ⊢
  rw [projectivePointOfVector_mem_iff v hv hp] at hm
  have hrel : v (other i) = t * v i := by
    simpa [p,sub_eq_zero] using hm
  rw [projectivePointOfVector_eq_iff_mk_eq]
  apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
  refine ⟨v i,?_⟩
  funext j
  fin_cases i <;> fin_cases j <;> simp [chartVector,other,mul_comm] at hrel ⊢ <;> exact hrel.symm

@[simp] theorem chart_one_affinePoint (t : k) :
    (projectiveLineChartInclusion (k := k) 1) (affinePoint t) = projectiveLineAffinePoint t := by
  rw [chartInclusion_affinePoint]
  congr 1
  funext i
  fin_cases i <;> simp [chartVector,projectiveLineAffineVector]

@[simp] theorem chart_zero_affinePoint (t : k) :
    (projectiveLineChartInclusion (k := k) 0) (affinePoint t) = projectiveLineInfinityChartPoint t := by
  rw [chartInclusion_affinePoint]
  congr 1
  funext i
  fin_cases i <;> simp [chartVector,projectiveLineInfinityChartVector]

end
end Theory.AlgebraicGroup.Variety.Geometric.ProjectiveLineAutomorphisms
