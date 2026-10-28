module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.ExtensionClasses.Reduction
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.ExtensionClasses.Homogeneous.Calculation

/-!
# Splitting natural self-extensions of the binary SL₃(4) module

A cross block normalized at the central scalar is F₄-linear. In those
coordinates, the small matrix calculation in `Homogeneous.Calculation`
constructs a coboundary. Restricting its scalars gives a binary section change
and an actual representation equivalence with the split extension.

This is the homogeneous extension calculation used in the local catalogue
for James (1973), Lemma 8.3, cited in Aschbacher–Smith H.12.1, printed
pp.393–394. No constituent-completeness or Ext-vanishing premise is used.
-/

@[expose] public noncomputable section
namespace Representation.SL3FourLocalCatalogue.BlockCocycle

private lemma natural_field_smul (r : F) (v : W) :
    r • v = r.re • v + r.im • constituent .natural z v := by
  change r • v = r.re • v + r.im • SL3FourNaturalDual.natural z v
  rw [SL3FourNaturalDual.centralScalar_natural]
  conv_lhs => rw [show r = algebraMap (ZMod 2) F r.re + r.im • SL3FourNaturalDual.omega from
    QuadraticAlgebra.mk_eq_add_smul_omega r.re r.im]
  rw [add_smul, algebraMap_smul, smul_assoc]

private def fieldValue (c : BlockCocycle .natural .natural) (hc : c.value z = 0)
    (g : SL) : W →ₗ[F] W where
  toFun := c.value g
  map_add' := (c.value g).map_add
  map_smul' r v := by
    change c.value g (r • v) = r • c.value g v
    rw [natural_field_smul, c.normalized_field_smul hc, ← natural_field_smul]

/-- A normalized self-extension of the actual natural binary SL₃(4) module
is a coboundary on every group element. -/
lemma normalized_natural_coboundary (c : BlockCocycle .natural .natural)
    (hc : c.value z = 0) :
    ∃ f : W →ₗ[ZMod 2] W, ∀ g : SL,
      c.value g + f.comp (constituent .natural g) = (constituent .natural g).comp f := by
  let C (g : SL) := LinearMap.toMatrix' (fieldValue c hc g)
  have h1 : C 1 = 0 := by
    have h : fieldValue c hc 1 = 0 := by
      apply LinearMap.ext
      intro v
      exact LinearMap.congr_fun c.one v
    simp only [C, h, map_zero]
  have hm (g h : SL) : C (g*h) = g.val * C h + C g * h.val := by
    have he : fieldValue c hc (g*h) =
        g.val.toLin'.comp (fieldValue c hc h) + (fieldValue c hc g).comp h.val.toLin' := by
      apply LinearMap.ext
      intro v
      exact LinearMap.congr_fun (c.mul g h) v
    simp only [C, he, map_add, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
  obtain ⟨M, hM⟩ := HomogeneousCalculation.matrix_coboundary C h1 hm
  refine ⟨M.toLin'.restrictScalars (ZMod 2), ?_⟩
  intro g
  have he := congrArg Matrix.toLin' (hM g)
  have hh : fieldValue c hc g + M.toLin'.comp g.val.toLin' =
      g.val.toLin'.comp M.toLin' := by
    simpa only [C, map_add, Matrix.toLin'_toMatrix', Matrix.toLin'_mul] using he
  apply LinearMap.ext
  intro v
  exact LinearMap.congr_fun hh v

/-- The actual binary intertwining equivalence splitting a normalized natural
self-extension. Its underlying linear equivalence changes the section. -/
def normalizedNaturalSplitEquiv (c : BlockCocycle .natural .natural)
    (hc : c.value z = 0) :
    c.representation.Equiv (zero .natural .natural).representation := by
  let h := normalized_natural_coboundary c hc
  apply equivOfCoboundary c (zero .natural .natural) h.choose
  intro g
  simpa only [zero, add_zero] using h.choose_spec g

end Representation.SL3FourLocalCatalogue.BlockCocycle
