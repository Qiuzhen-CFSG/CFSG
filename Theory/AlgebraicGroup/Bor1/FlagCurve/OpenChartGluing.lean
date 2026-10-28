module

public import Theory.AlgebraicGroup.Variety.OpenSubvariety
public import Theory.AlgebraicGroup.Variety.ProjectivePolynomialCurve

/-!
# Compatibility on open charts from rational points

For morphisms over an algebraically closed field, equality on rational points
of an open-chart overlap gives equality of the scheme morphisms. The overlap
is reduced because its projection is an open immersion. This is the precise
compatibility test used to glue the monomial parametrizations in Borel §13.13.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Theory.AlgebraicGroup.Variety.Geometric
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

set_option backward.isDefEq.respectTransparency false in
theorem open_chart_compatible_of_points
    {X Y U V : Theory.AlgebraicGroup.Variety.Geometric k}
    (i : Morphism U X) (j : Morphism V X)
    [IsOpenImmersion i.hom] [IsOpenImmersion j.hom]
    (f : Morphism U Y) (g : Morphism V Y)
    (h : ∀ u : Point U, ∀ v : Point V, i u = j v → f u = g v) :
    pullback.fst i.hom j.hom ≫ f.hom = pullback.snd i.hom j.hom ≫ g.hom := by
  let D := pullback i.hom j.hom
  let s : D ⟶ Spec (.of k) := pullback.fst i.hom j.hom ≫ U.structureMap
  have : IsReduced D := isReduced_of_isOpenImmersion (pullback.fst i.hom j.hom)
  have hs : pullback.snd i.hom j.hom ≫ V.structureMap = s := by
    rw [← j.commutes, ← Category.assoc, ← pullback.condition, Category.assoc, i.commutes]
  have hf : (pullback.fst i.hom j.hom ≫ f.hom) ≫ Y.structureMap = s := by
    rw [Category.assoc, f.commutes]
  have hg : (pullback.snd i.hom j.hom ≫ g.hom) ≫ Y.structureMap = s := by
    rw [Category.assoc, g.commutes, hs]
  have : LocallyOfFiniteType s := by dsimp [s]; infer_instance
  have : LocallyOfFiniteType ((pullback.fst i.hom j.hom ≫ f.hom) ≫ Y.structureMap) :=
    hf ▸ inferInstance
  apply AlgebraicGeometry.ext_of_apply_eq Y.structureMap Set.univ
    isOpen_univ.isLocallyClosed dense_univ _ (hf.trans hg.symm)
  intro z _ hz
  let q := pointOfClosedPoint s z hz
  have hq : q ≫ s = 𝟙 _ := pointOfClosedPoint_comp s z hz
  let u : Point U := ⟨q ≫ pullback.fst i.hom j.hom, by simpa [s, Category.assoc] using hq⟩
  let v : Point V := ⟨q ≫ pullback.snd i.hom j.hom, by simpa [Category.assoc, hs] using hq⟩
  have huv : i u = j v := by
    apply Subtype.ext
    exact congrArg (fun z => q ≫ z) (pullback.condition (f := i.hom) (g := j.hom))
  have he := congrArg (fun p : Point Y => p.1 (IsLocalRing.closedPoint k)) (h u v huv)
  have hzq : q (IsLocalRing.closedPoint k) = z := pointOfClosedPoint_apply s z hz _
  simpa only [Morphism.coe_apply, Scheme.Hom.comp_apply, u, v, hzq] using he

end Theory.AlgebraicGroup.Bor1.FlagCurve
