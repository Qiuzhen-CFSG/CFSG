module

public import Theory.AlgebraicGroup.Variety.ProjectiveLineAutomorphisms.Rigidity
public import Theory.AlgebraicGroup.Variety.ProjectiveLineAutomorphisms.Triples

import all Theory.AlgebraicGroup.Instance.PGL2ProjectiveAction

/-!
# The actual PGL₂ point homomorphism of a projective-line action

An inverse pair of geometric projective-line maps sends the three named points
to a distinct triple. The actual PGL₂ triple theorem supplies its unique matching
transformation. Composing with its inverse gives a genuine scheme automorphism
fixing the three marks, so three-point rigidity proves agreement everywhere.

Applied to each translation of an original morphic action, this construction is
a group homomorphism on actual group points. Multiplicativity and uniqueness
follow from action agreement, and the final consumer identifies the translation
scheme morphisms themselves. This is the point-level part of Borel 10.8/13.13;
algebraic regularity in the acting parameter is proved separately.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
namespace Theory.AlgebraicGroup.Variety.Geometric.ProjectiveLineAutomorphisms
noncomputable section
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
local instance : MulAction (Variety.Point (pgl2Variety (k := k)))
    (Point (projectiveLine k)) := pgl2ProjectiveLinePointMulAction

private theorem pgl_translation_apply (a : Variety.Point (pgl2Variety (k := k)))
    (p : Point (projectiveLine k)) :
    (pgl2ProjectiveLineMorphicAction (k := k)).translationMorphism a p = a • p :=
  (pgl2ProjectiveLineMorphicAction (k := k)).translationMorphism_apply a p

private theorem pgl_eq_of_smul_eq (a b : Variety.Point (pgl2Variety (k := k)))
    (h : ∀ p : Point (projectiveLine k), a • p = b • p) : a = b :=
  pgl2_triple_images_injective a b (h _) (h _) (h _)

set_option backward.isDefEq.respectTransparency false in
/-- Every genuine projective-line automorphism acts by a unique actual PGL₂ point. -/
theorem existsUnique_pgl2_of_inverse
    (f g : Morphism (projectiveLine k) (projectiveLine k))
    (hfg : Morphism.comp f g = Morphism.id (projectiveLine k))
    (hgf : Morphism.comp g f = Morphism.id (projectiveLine k)) :
    ∃! a : Variety.Point (pgl2Variety (k := k)), ∀ p : Point (projectiveLine k), a • p = f p := by
  have hfgp : ∀ p, g (f p) = p := by
    intro p
    simpa only [Morphism.comp_apply_point,Morphism.id_apply_point] using
      congrArg (fun m : Morphism (projectiveLine k) (projectiveLine k) => m p) hfg
  have hgfp : ∀ p, f (g p) = p := by
    intro p
    simpa only [Morphism.comp_apply_point,Morphism.id_apply_point] using
      congrArg (fun m : Morphism (projectiveLine k) (projectiveLine k) => m p) hgf
  have hfinj : Function.Injective f := Function.LeftInverse.injective (g := fun p => g p) hfgp
  have h10 : projectiveLineOne (k := k) ≠ projectiveLineZero := by
    exact fun he => one_ne_zero (projectiveLineAffinePoint_injective he)
  obtain ⟨a,ha,-⟩ := existsUnique_pgl2_of_distinct_points
    (f projectiveLineZero) (f projectiveLineOne) (f projectiveLineInfinity)
    (fun he => h10 (hfinj he))
    (fun he => projectiveLineInfinity_ne_affinePoint 1 (hfinj he))
    (fun he => projectiveLineInfinity_ne_affinePoint 0 (hfinj he))
  let σ : Variety.Point (pgl2Variety (k := k)) → Point (projectiveLine k) →
      Point (projectiveLine k) := fun b p => b • p
  have hc₁ (p : Point (projectiveLine k)) : σ a (σ a⁻¹ p) = p := smul_inv_smul a p
  have hc₂ (p : Point (projectiveLine k)) : σ a⁻¹ (σ a p) = p := inv_smul_smul a p
  let T := (pgl2ProjectiveLineMorphicAction (k := k)).translationMorphism
  let U := Morphism.comp f (T a⁻¹)
  let V := Morphism.comp (T a) g
  have hU (p : Point (projectiveLine k)) : U p = σ a⁻¹ (f p) :=
    (Morphism.comp_apply_point f (T a⁻¹) p).trans (pgl_translation_apply a⁻¹ (f p))
  have hV (p : Point (projectiveLine k)) : V p = g (σ a p) :=
    (Morphism.comp_apply_point (T a) g p).trans
      (congrArg (fun q : Point (projectiveLine k) => g q) (pgl_translation_apply a p))
  have hinv₁ : Morphism.comp U V = Morphism.id (projectiveLine k) := by
    apply morphism_eq_of_pointwise_eq
    intro p
    calc
      Morphism.comp U V p = V (U p) := Morphism.comp_apply_point U V p
      _ = g (σ a (U p)) := hV (U p)
      _ = g (σ a (σ a⁻¹ (f p))) := congrArg (fun q => g (σ a q)) (hU p)
      _ = g (f p) := congrArg (fun q => g q) (hc₁ (f p))
      _ = Morphism.id (projectiveLine k) p := (hfgp p).trans (Morphism.id_apply_point p).symm
  have hinv₂ : Morphism.comp V U = Morphism.id (projectiveLine k) := by
    apply morphism_eq_of_pointwise_eq
    intro p
    calc
      Morphism.comp V U p = U (V p) := Morphism.comp_apply_point V U p
      _ = σ a⁻¹ (f (V p)) := hU (V p)
      _ = σ a⁻¹ (f (g (σ a p))) := congrArg (fun q => σ a⁻¹ (f q)) (hV p)
      _ = σ a⁻¹ (σ a p) := congrArg (σ a⁻¹) (hgfp (σ a p))
      _ = Morphism.id (projectiveLine k) p := (hc₂ p).trans (Morphism.id_apply_point p).symm
  have hfix (p : Point (projectiveLine k)) (hp : σ a p = f p) : U p = p :=
    (hU p).trans ((congrArg (σ a⁻¹) hp.symm).trans (hc₂ p))
  have hn := projectiveLine_morphism_eq_id_of_inverse_fix_three U V hinv₁ hinv₂
    (hfix _ ha.1) (hfix _ ha.2.1) (hfix _ ha.2.2)
  have hall : ∀ p : Point (projectiveLine k), a • p = f p := by
    intro p
    have hh : U p = p :=
      (congrArg (fun m : Morphism (projectiveLine k) (projectiveLine k) => m p) hn).trans
        (Morphism.id_apply_point p)
    exact (congrArg (σ a) ((hU p).symm.trans hh)).symm.trans (hc₁ (f p))
  refine ⟨a,hall,?_⟩
  intro b hb
  exact pgl_eq_of_smul_eq b a (fun p => (hb p).trans (hall p).symm)

variable {H : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup H]

/-- The actual PGL₂ point determined by a translation of the given morphic action. -/
def actionPoint (A : MorphicAction H (projectiveLine k)) (h : Variety.Point H) :
    Variety.Point (pgl2Variety (k := k)) :=
  Classical.choose (existsUnique_pgl2_of_inverse (A.translationMorphism h)
    (A.translationMorphism h⁻¹) (A.translationMorphism_comp_inv h)
    (A.translationMorphism_inv_comp h)).exists

set_option backward.isDefEq.respectTransparency false in
theorem actionPoint_smul (A : MorphicAction H (projectiveLine k)) (h : Variety.Point H)
    (p : Point (projectiveLine k)) : actionPoint A h • p = A.toMulAction.smul h p := by
  have hh := Classical.choose_spec (existsUnique_pgl2_of_inverse (A.translationMorphism h)
    (A.translationMorphism h⁻¹) (A.translationMorphism_comp_inv h)
    (A.translationMorphism_inv_comp h)).exists p
  exact hh.trans (A.translationMorphism_apply h p)

/-- Point-level group homomorphism realizing an original morphic action on P¹. -/
def pointActionHom (A : MorphicAction H (projectiveLine k)) :
    Variety.Point H →* Variety.Point (pgl2Variety (k := k)) where
  toFun := actionPoint A
  map_one' := by
    apply pgl_eq_of_smul_eq
    intro p
    rw [actionPoint_smul,one_smul]
    exact A.toMulAction.one_smul p
  map_mul' h j := by
    apply pgl_eq_of_smul_eq
    intro p
    rw [actionPoint_smul,mul_smul,actionPoint_smul,actionPoint_smul]
    exact A.toMulAction.mul_smul h j p

@[simp] theorem pointActionHom_smul (A : MorphicAction H (projectiveLine k))
    (h : Variety.Point H) (p : Point (projectiveLine k)) :
    pointActionHom A h • p = A.toMulAction.smul h p := actionPoint_smul A h p

theorem pointActionHom_unique (A : MorphicAction H (projectiveLine k))
    (φ : Variety.Point H →* Variety.Point (pgl2Variety (k := k)))
    (hφ : ∀ h p, φ h • p = A.toMulAction.smul h p) : φ = pointActionHom A := by
  apply MonoidHom.ext
  intro h
  exact pgl_eq_of_smul_eq _ _ (fun p => (hφ h p).trans (pointActionHom_smul A h p).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The induced point homomorphism agrees with each translation as a scheme morphism. -/
theorem pointActionHom_translation (A : MorphicAction H (projectiveLine k))
    (h : Variety.Point H) :
    (pgl2ProjectiveLineMorphicAction (k := k)).translationMorphism (pointActionHom A h) =
      A.translationMorphism h := by
  apply morphism_eq_of_pointwise_eq
  intro p
  rw [pgl_translation_apply,A.translationMorphism_apply,pointActionHom_smul]

end
end Theory.AlgebraicGroup.Variety.Geometric.ProjectiveLineAutomorphisms
