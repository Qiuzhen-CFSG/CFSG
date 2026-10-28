module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootTorus.Coordinates

/-!
# Regular coroot products from regular root curves

Composition with the ordinary coordinate and negative inverse coordinate maps
makes the source normalizer words regular. Left translation by `n(1)⁻¹` gives
the coroot maps, and their ordered product is regular. Its group law follows
from the point identities in `CorootPoints` and `Coordinates`.

The actual regular root curves are explicit inputs to this helper. No inverse
to the Spin cover is used. Source: GLS3, Theorem 1.12.1 and 1.12.5(b),
`refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
noncomputable section
namespace Triality.SimplyConnected.Pinning.CorootTorus
open Theory Theory.AlgebraicGroup
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

private def additiveCoordinate (i : Fin 4) (inverse : Bool) :
    Variety.Morphism (dVariety k 4) (KPlus k) where
  toFun x := kPlusPoint (if inverse then -x.val (Sum.inr (ULift.up i))
    else x.val (Sum.inl (ULift.up i)))
  regular := by
    intro c
    cases inverse
    · refine ⟨MvPolynomial.X (Sum.inl (ULift.up i)), ?_⟩
      intro x
      change x.val (Sum.inl (ULift.up i)) =
        evalPolynomial x.val (MvPolynomial.X (Sum.inl (ULift.up i)))
      rw [evalPolynomial_X]
    · refine ⟨-MvPolynomial.X (Sum.inr (ULift.up i)), ?_⟩
      intro x
      change -x.val (Sum.inr (ULift.up i)) =
        evalPolynomial x.val (-MvPolynomial.X (Sum.inr (ULift.up i)))
      simp [evalPolynomial]

omit [IsAlgClosed k] [CharP k 2] in
private theorem additiveCoordinate_apply (i : Fin 4) (inverse : Bool)
    (x : Variety.Point (dVariety k 4)) :
    (additiveCoordinate k i inverse).toFun x =
      kPlusPoint (if inverse then -((dPointEquiv 4 x i : k)⁻¹)
        else (dPointEquiv 4 x i : k)) := by
  cases inverse
  · rfl
  · change kPlusPoint (-((↑((dPointEquiv 4 x i)⁻¹) : k))) = _
    simp

private def wordMultiply
    (f g : Variety.Morphism (dVariety k 4) (groupVariety k)) :
    Variety.Morphism (dVariety k 4) (groupVariety k) :=
  (mulMorphism (groupVariety k)).comp (f.pair g)

private def wordProduct : List (Variety.Morphism (dVariety k 4) (groupVariety k)) →
    Variety.Morphism (dVariety k 4) (groupVariety k)
  | [] => Variety.Morphism.const _ _ 1
  | f :: fs => wordMultiply k f (wordProduct fs)

omit [CharP k 2] in
private theorem wordProduct_apply
    (fs : List (Variety.Morphism (dVariety k 4) (groupVariety k)))
    (x : Variety.Point (dVariety k 4)) :
    (wordProduct k fs).toFun x = (fs.map fun f => f.toFun x).prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    change f.toFun x * (wordProduct k fs).toFun x = _
    rw [ih]
    rfl

private def simpleCorootVarietyMorphism
    (ρ : RootIndex → AlgebraicGroup.Morphism (KPlus k) (groupVariety k)) (i : Fin 4) :
    Variety.Morphism (dVariety k 4) (groupVariety k) :=
  let positive := (ρ (simpleRoot i)).toVariety.comp (additiveCoordinate k i false)
  let negative := (ρ (negativeSimpleRoot i)).toVariety.comp (additiveCoordinate k i true)
  (leftMulMorphism (groupVariety k) (simpleNormalizer k i)⁻¹).comp
    (wordMultiply k (wordMultiply k positive negative) positive)

private theorem simpleCorootVarietyMorphism_apply
    (ρ : RootIndex → AlgebraicGroup.Morphism (KPlus k) (groupVariety k))
    (hρ : ∀ r a, (ρ r).onPoints (kPlusPoint a) = rootPoint k r a)
    (i : Fin 4) (x : Variety.Point (dVariety k 4)) :
    (simpleCorootVarietyMorphism k ρ i).toFun x =
      simpleCoroot k i (dPointEquiv 4 x i) := by
  change (simpleNormalizer k i)⁻¹ *
      (((ρ (simpleRoot i)).onPoints ((additiveCoordinate k i false).toFun x) *
        (ρ (negativeSimpleRoot i)).onPoints ((additiveCoordinate k i true).toFun x)) *
        (ρ (simpleRoot i)).onPoints ((additiveCoordinate k i false).toFun x)) = _
  simp only [additiveCoordinate_apply, Bool.false_eq_true, ↓reduceIte, hρ]
  rfl

private theorem regularProduct_apply
    (ρ : RootIndex → AlgebraicGroup.Morphism (KPlus k) (groupVariety k))
    (hρ : ∀ r a, (ρ r).onPoints (kPlusPoint a) = rootPoint k r a)
    (x : Variety.Point (dVariety k 4)) :
    (wordProduct k (List.ofFn (simpleCorootVarietyMorphism k ρ))).toFun x =
      parameter k (dPointEquiv 4 x) := by
  rw [wordProduct_apply, List.map_ofFn, parameter]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  exact simpleCorootVarietyMorphism_apply k ρ hρ i x

/-- Regular root curves give the regular coroot product without any use of
an inverse to the Spin cover. Its group law is the already proved point law. -/
def productOfRegularRoots
    (ρ : RootIndex → AlgebraicGroup.Morphism (KPlus k) (groupVariety k))
    (hρ : ∀ r a, (ρ r).onPoints (kPlusPoint a) = rootPoint k r a) :
    AlgebraicGroup.Morphism (dVariety k 4) (groupVariety k) where
  toVariety := wordProduct k (List.ofFn (simpleCorootVarietyMorphism k ρ))
  map_one := by rw [regularProduct_apply k ρ hρ, dPointEquiv_one, parameter_one]
  map_mul x y := by
    simp only [regularProduct_apply k ρ hρ, dPointEquiv_mul, parameter_mul]

/-- The regular product has precisely the published simple-coroot point formula. -/
theorem productOfRegularRoots_apply
    (ρ : RootIndex → AlgebraicGroup.Morphism (KPlus k) (groupVariety k))
    (hρ : ∀ r a, (ρ r).onPoints (kPlusPoint a) = rootPoint k r a)
    (x : Variety.Point (dVariety k 4)) :
    (productOfRegularRoots k ρ hρ).onPoints x = parameter k (dPointEquiv 4 x) :=
  regularProduct_apply k ρ hρ x

end Triality.SimplyConnected.Pinning.CorootTorus
