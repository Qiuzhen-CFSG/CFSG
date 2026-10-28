module
public import Theory.AlgebraicGroup.Variety.GlobalSectionCoordinates
public import Theory.AlgebraicGroup.Instance.GL
public import Theory.AlgebraicGroup.Variety.ProjectiveLineAutomorphisms.Charts

/-!
# Matrix families from geometric regular sections

A matrix of global sections with nowhere-zero determinant gives a genuine map
to GL₂: its determinant is a unit by the rational-point criterion, and the
inverse coordinate is its ring inverse. The matrix is preserved on points.
We also pull the actual polynomial affine coordinate back along a geometric
map and verify its evaluation. These two constructions produce the regular
matrices on projective charts used in Borel, §10.8.
-/

open scoped MatrixGroups
open CategoryTheory AlgebraicGeometry
namespace Theory.AlgebraicGroup.Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
public noncomputable section

def matrixOfSections {V : Geometric k} (M : Matrix (Fin 2) (Fin 2) Γ(V.toScheme, ⊤))
    (hM : ∀ x : Point V, (M.map (sectionEvaluation V x)).det ≠ 0) :
    Morphism V (ofAffine (glVariety 2 : Variety k)) := by
  let ψ (x : Point V) : Variety.Point (glVariety 2 : Variety k) :=
    (glPointEquiv 2).symm (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hM x))
  have hu : IsUnit M.det := section_isUnit_of_evaluations V M.det (fun x => by
    rw [(sectionEvaluation V x).map_det]
    exact hM x)
  let c : (glVariety 2 : Variety k).Coordinates → Γ(V.toScheme, ⊤) :=
    Sum.elim (fun ij => M ij.1 ij.2) (fun _ => (hu.unit⁻¹).val)
  refine morphismOfSectionCoordinates ψ c ?_
  intro x i
  cases i with
  | inl ij => rfl
  | inr _ =>
      change sectionEvaluation V x (hu.unit⁻¹).val = (M.map (sectionEvaluation V x)).det⁻¹
      have hh : sectionEvaluation V x M.det * sectionEvaluation V x (hu.unit⁻¹).val = 1 := by
        simpa only [map_mul, map_one] using congrArg (sectionEvaluation V x) hu.mul_val_inv
      rw [(sectionEvaluation V x).map_det] at hh
      exact eq_inv_of_mul_eq_one_right hh

lemma matrixOfSections_apply {V : Geometric k} (M : Matrix (Fin 2) (Fin 2) Γ(V.toScheme, ⊤))
    (hM : ∀ x : Point V, (M.map (sectionEvaluation V x)).det ≠ 0) (x : Point V) :
    affinePointEquiv (glVariety 2 : Variety k) (matrixOfSections M hM x) =
      (glPointEquiv 2).symm (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hM x)) := by
  exact morphismOfSectionCoordinates_apply _ _ _ x

namespace ProjectiveLineAutomorphisms

def affineCoordinateSection {V : Geometric k} (f : Morphism V (polynomialAffineLine k)) :
    Γ(V.toScheme, ⊤) :=
  f.hom.appTop ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X)

omit [IsAlgClosed k] in
lemma affineCoordinateSection_evaluation {V : Geometric k}
    (f : Morphism V (polynomialAffineLine k)) (x : Point V) (t : k)
    (ht : f x = affinePoint t) : sectionEvaluation V x (affineCoordinateSection f) = t := by
  have hh : x.1 ≫ f.hom = (affinePoint t).1 := congrArg Subtype.val ht
  change (Scheme.ΓSpecIso (.of k)).hom (x.1.appTop
    (f.hom.appTop ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X))) = t
  have he : f.hom.appTop ≫ x.1.appTop = (affinePoint t).1.appTop := by
    rw [← Scheme.Hom.comp_appTop, hh]
  have hev := congrArg (fun φ => φ ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X)) he
  change x.1.appTop (f.hom.appTop ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X)) =
    (affinePoint t).1.appTop ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X) at hev
  rw [hev]
  change (Scheme.ΓSpecIso (.of k)).hom ((Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom t))).appTop
    ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X)) = t
  have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Polynomial.evalRingHom t))
  have hnX := congrArg (fun φ => φ Polynomial.X) hn
  change (Scheme.ΓSpecIso (.of k)).inv ((Polynomial.evalRingHom t) Polynomial.X) =
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom t))).appTop
      ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X) at hnX
  rw [← hnX]
  simp

omit [IsAlgClosed k] in
lemma affineCoordinateSection_spec {V : Geometric k}
    (f : Morphism V (polynomialAffineLine k)) (x : Point V) :
    f x = affinePoint (sectionEvaluation V x (affineCoordinateSection f)) := by
  obtain ⟨t, ht⟩ := affinePoint_surjective (f x)
  rw [affineCoordinateSection_evaluation f x t ht.symm]
  exact ht.symm

end ProjectiveLineAutomorphisms
end
end Theory.AlgebraicGroup.Variety.Geometric
