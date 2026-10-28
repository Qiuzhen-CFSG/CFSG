module

public import Theory.AlgebraicGroup.Jordan.Components
public import Theory.AlgebraicGroup.Morphism.Basic

universe u

/-! Preservation of Jordan components by algebraic-group morphisms. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Pullback along an algebraic-group morphism intertwines the right regular
actions of a point and its image. -/
public lemma Morphism.pullback_intertwines_rightTranslation
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism G H) (g : Variety.Point G) :
    φ.toVariety.pullbackAlgHom.toLinearMap.comp
        (rightTranslationPullback H (φ.onPoints g)) =
      (rightTranslationPullback G g).comp
        φ.toVariety.pullbackAlgHom.toLinearMap := by
  apply LinearMap.ext
  intro f
  apply Variety.PolynomialFunction.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  change rightTranslationPullback H (φ.onPoints g) f (φ.onPoints x) =
    φ.toVariety.pullbackAlgHom.toLinearMap f (x * g)
  rw [rightTranslationPullback_apply]
  change f (φ.onPoints x * φ.onPoints g) = f (φ.onPoints (x * g))
  rw [φ.onPoints.map_mul]

/-- An algebraic-group morphism maps the Jordan components of a point to the
Jordan components of its image. -/
public lemma Morphism.maps_jordanComponents
    [IsAlgClosed k] {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism G H) (g : Variety.Point G)
    (dG : JordanDecomposition g)
    (dH : JordanDecomposition (φ.onPoints g)) :
    dH.semisimplePart = φ.onPoints dG.semisimplePart ∧
      dH.unipotentPart = φ.onPoints dG.unipotentPart := by
  let TG : Module.End k (Variety.PolynomialFunction G) :=
    rightTranslationPullback G g
  let TH : Module.End k (Variety.PolynomialFunction H) :=
    rightTranslationPullback H (φ.onPoints g)
  have hTGloc : Module.End.IsLocallyFinite TG :=
    rightTranslationPullback_locallyFinite G g
  have hTHloc : Module.End.IsLocallyFinite TH :=
    rightTranslationPullback_locallyFinite H (φ.onPoints g)
  let L : Variety.PolynomialFunction H →ₗ[k] Variety.PolynomialFunction G :=
    φ.toVariety.pullbackAlgHom.toLinearMap
  have hinter : L.comp TH = TG.comp L :=
    φ.pullback_intertwines_rightTranslation g
  have hsemi := hTHloc.semisimplePart_semiconj hTGloc L hinter
  have hsemi' : L.comp (rightTranslationPullback H dH.semisimplePart) =
      (rightTranslationPullback G dG.semisimplePart).comp L := by
    rw [← dH.semisimplePart_pullback, ← dG.semisimplePart_pullback]
    exact hsemi
  have hs : dH.semisimplePart = φ.onPoints dG.semisimplePart := by
    apply Variety.Point.ext
    funext i
    let f := Variety.PolynomialFunction.ofPolynomial H (MvPolynomial.X i)
    have h := LinearMap.congr_fun hsemi' f
    have h1 := congrArg
      (fun q : Variety.PolynomialFunction G => q 1) h
    change f (φ.onPoints (1 : Variety.Point G) * dH.semisimplePart) =
      f (φ.onPoints ((1 : Variety.Point G) * dG.semisimplePart)) at h1
    rw [φ.onPoints.map_one, one_mul, one_mul] at h1
    simpa [f, Variety.PolynomialFunction.ofPolynomial,
      Variety.PolynomialFunction.toFun, evalPolynomial] using h1
  refine ⟨hs, ?_⟩
  have hmapdec : φ.onPoints g =
      φ.onPoints dG.semisimplePart * φ.onPoints dG.unipotentPart := by
    rw [← φ.onPoints.map_mul, ← dG.eq_mul]
  have hdecH := dH.eq_mul
  rw [hs] at hdecH
  exact mul_left_cancel (hdecH.symm.trans hmapdec)

/-! ## Morphisms preserve Jordan type -/

/-- GLS Proposition 1.2.2(a), semisimple case. -/
public theorem morphism_preserves_semisimpleElement
    [IsAlgClosed k] {G H : Variety k}
    [AlgebraicGroup G] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism G H) (g : Variety.Point G)
    (hg : IsSemisimpleElement G g) :
    IsSemisimpleElement H (φ.onPoints g) := by
  let dG := jordanDecomposition g
  let dH := jordanDecomposition (φ.onPoints g)
  let trivial : JordanDecomposition g :=
    { semisimplePart := g
      unipotentPart := 1
      eq_mul := by simp
      commute := Commute.one_right g
      semisimple := hg
      unipotent := one_isUnipotentElement G }
  have hdG : dG = trivial := dG.unique trivial
  have hsG : dG.semisimplePart = g :=
    congrArg JordanDecomposition.semisimplePart hdG
  have hmap := φ.maps_jordanComponents g dG dH
  have hsemiH := dH.semisimple
  rw [hmap.1, hsG] at hsemiH
  exact hsemiH

/-- GLS Proposition 1.2.2(a), unipotent case. -/
public theorem morphism_preserves_unipotentElement
    [IsAlgClosed k] {G H : Variety k}
    [AlgebraicGroup G] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism G H) (g : Variety.Point G)
    (hg : IsUnipotentElement G g) :
    IsUnipotentElement H (φ.onPoints g) := by
  let dG := jordanDecomposition g
  let dH := jordanDecomposition (φ.onPoints g)
  let trivial : JordanDecomposition g :=
    { semisimplePart := 1
      unipotentPart := g
      eq_mul := by simp
      commute := Commute.one_left g
      semisimple := one_isSemisimpleElement G
      unipotent := hg }
  have hdG : dG = trivial := dG.unique trivial
  have huG : dG.unipotentPart = g :=
    congrArg JordanDecomposition.unipotentPart hdG
  have hmap := φ.maps_jordanComponents g dG dH
  have huniH := dH.unipotent
  rw [hmap.2, huG] at huniH
  exact huniH

end Theory.AlgebraicGroup
