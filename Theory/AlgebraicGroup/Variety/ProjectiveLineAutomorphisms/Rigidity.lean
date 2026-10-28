module

public import Theory.AlgebraicGroup.Variety.ProjectiveLineAutomorphisms.OpenFactorization
public import Theory.AlgebraicGroup.Variety.ProjectiveLineAutomorphisms.ChartComplement
public import Theory.AlgebraicGroup.Bor1.MorphicActionSchemeLaws

import all Theory.AlgebraicGroup.Instance.PGL2ProjectiveAction

/-!
# Three-point rigidity for genuine projective-line automorphisms

An inverse pair of morphisms over an algebraically closed field, with the
forward map fixing zero, one, and infinity, has forward map equal to the scheme
identity. Fixing infinity preserves the actual affine chart. The open-immersion
universal property restricts both maps to affine morphisms, whose pullback
polynomials are inverse. Degree multiplicativity and the two finite fixed
points force the coordinate polynomial to be X. Closed-point extensionality
then proves equality of the original projective scheme maps.

This is Borel, Linear Algebraic Groups, 10.8, including characteristic two.
The final consumer applies the result to an original morphic action using its
proved translation-by-inverse scheme laws. No separability, polynomial-action
certificate, or projective-linear realization is assumed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
namespace Theory.AlgebraicGroup.Variety.Geometric.ProjectiveLineAutomorphisms
noncomputable section
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

set_option backward.isDefEq.respectTransparency false in
private theorem chart_preserved (f : Morphism (projectiveLine k) (projectiveLine k))
    (hf : Function.Injective f) (hi : f projectiveLineInfinity = projectiveLineInfinity) :
    ∀ p : Point (polynomialAffineLine k),
      ((Morphism.comp (projectiveLineChartInclusion 1) f) p).val
        (IsLocalRing.closedPoint k) ∈ projectiveLineChartOpen k 1 := by
  intro p
  rw [Morphism.comp_apply_point,point_mem_chart_one_iff_ne_infinity]
  intro he
  have hpi : projectiveLineChartInclusion 1 p = projectiveLineInfinity := hf (he.trans hi.symm)
  have hmem := (point_mem_chart_iff 1 (projectiveLineChartInclusion 1 p)).mpr ⟨p,rfl⟩
  exact (point_mem_chart_one_iff_ne_infinity _).mp hmem hpi

set_option backward.isDefEq.respectTransparency false in
/-- An automorphism over k fixing zero, one, and infinity is the identity. -/
theorem projectiveLine_morphism_eq_id_of_inverse_fix_three
    (f g : Morphism (projectiveLine k) (projectiveLine k))
    (hfg : Morphism.comp f g = Morphism.id (projectiveLine k))
    (hgf : Morphism.comp g f = Morphism.id (projectiveLine k))
    (h0 : f projectiveLineZero = projectiveLineZero)
    (h1 : f projectiveLineOne = projectiveLineOne)
    (hi : f projectiveLineInfinity = projectiveLineInfinity) :
    f = Morphism.id (projectiveLine k) := by
  have hfgp : ∀ p, g (f p) = p := by
    intro p
    simpa only [Morphism.comp_apply_point,Morphism.id_apply_point] using
      congrArg (fun m : Morphism (projectiveLine k) (projectiveLine k) => m p) hfg
  have hgfp : ∀ p, f (g p) = p := by
    intro p
    simpa only [Morphism.comp_apply_point,Morphism.id_apply_point] using
      congrArg (fun m : Morphism (projectiveLine k) (projectiveLine k) => m p) hgf
  have hfinj : Function.Injective f := Function.LeftInverse.injective (g := fun p => g p) hfgp
  have hginj : Function.Injective g := Function.LeftInverse.injective (g := fun p => f p) hgfp
  have hgi : g projectiveLineInfinity = projectiveLineInfinity := by
    exact (congrArg (fun p => g p) hi.symm).trans (hfgp projectiveLineInfinity)
  let F := chartLift 1 (Morphism.comp (projectiveLineChartInclusion 1) f)
    (chart_preserved f hfinj hi)
  let G := chartLift 1 (Morphism.comp (projectiveLineChartInclusion 1) g)
    (chart_preserved g hginj hgi)
  have hF (p : Point (polynomialAffineLine k)) :
      projectiveLineChartInclusion 1 (F p) = f (projectiveLineChartInclusion 1 p) := by
    exact (chartLift_apply 1 _ _ p).trans (Morphism.comp_apply_point _ _ p)
  have hG (p : Point (polynomialAffineLine k)) :
      projectiveLineChartInclusion 1 (G p) = g (projectiveLineChartInclusion 1 p) := by
    exact (chartLift_apply 1 _ _ p).trans (Morphism.comp_apply_point _ _ p)
  have hGF : Morphism.comp G F = Morphism.id (polynomialAffineLine k) := by
    apply morphism_eq_of_pointwise_eq
    intro p
    rw [Morphism.comp_apply_point,Morphism.id_apply_point]
    apply chartInclusion_injective 1
    rw [hF,hG,hgfp]
  have hF0 : F (affinePoint 0) = affinePoint 0 := by
    apply chartInclusion_injective 1
    rw [hF,chart_one_affinePoint]
    exact h0
  have hF1 : F (affinePoint 1) = affinePoint 1 := by
    apply chartInclusion_injective 1
    rw [hF,chart_one_affinePoint]
    exact h1
  have hFall := affineMorphism_pointwise_id_of_inverse_fix_zero_one F G hGF hF0 hF1
  apply morphism_eq_of_pointwise_eq
  intro p
  rw [Morphism.id_apply_point]
  by_cases hp : p = projectiveLineInfinity
  · subst p
    exact hi
  · have hm := (point_mem_chart_one_iff_ne_infinity p).mpr hp
    obtain ⟨x,rfl⟩ := (point_mem_chart_iff 1 p).mp hm
    rw [← hF,hFall]

set_option backward.isDefEq.respectTransparency false in
/-- Literal translation consumer for a morphic action on the projective line. -/
theorem translation_eq_id_of_fix_three
    {H : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup H]
    (A : MorphicAction H (projectiveLine k)) (h : Theory.AlgebraicGroup.Variety.Point H)
    (h0 : A.toMulAction.smul h projectiveLineZero = projectiveLineZero)
    (h1 : A.toMulAction.smul h projectiveLineOne = projectiveLineOne)
    (hi : A.toMulAction.smul h projectiveLineInfinity = projectiveLineInfinity) :
    A.translationMorphism h = Morphism.id (projectiveLine k) := by
  apply projectiveLine_morphism_eq_id_of_inverse_fix_three
    (A.translationMorphism h) (A.translationMorphism h⁻¹)
    (A.translationMorphism_comp_inv h) (A.translationMorphism_inv_comp h)
  · simpa only [MorphicAction.translationMorphism_apply] using h0
  · simpa only [MorphicAction.translationMorphism_apply] using h1
  · simpa only [MorphicAction.translationMorphism_apply] using hi

end
end Theory.AlgebraicGroup.Variety.Geometric.ProjectiveLineAutomorphisms
