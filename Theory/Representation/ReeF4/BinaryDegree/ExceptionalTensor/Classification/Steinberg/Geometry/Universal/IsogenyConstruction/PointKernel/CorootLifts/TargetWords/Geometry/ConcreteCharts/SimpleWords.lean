module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.RankOne
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.Transport
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.RootWeights

/-!
# Source-convention words for the literal simple F4 root pairs

In characteristic two each root element, and hence each three-factor
normalizer word, is an involution. Thus the GLS word `n(1)⁻¹n(t)` is the
inverse of the representation-coroot word `n(t)n(1)⁻¹`. The checked integral
simple-coroot calculation identifies the latter with the existing simple
cocharacter. Taking its inverse proves containment of the GLS word in the
literal split torus.

Consequently any regular SL₂ morphism agreeing with the literal positive and
negative simple root curves gives a rank-one chart, with no additional
premise about its diagonal image. The regular SL₂ morphism itself is still
an input; this module does not assert its existence.

Source: GLS3, Theorem 1.9.5(d), Remarks 1.9.6, and the defining formulas of
Theorem 1.12.1 in `refs/KGroup/GLS3/Chapter1.tex`.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
noncomputable section
namespace Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
local instance : InvolutiveNeg Root := typeF4RootPairing.indexNeg
local instance : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
  (splitTorus (k := k)).carrierAlgebraicGroup
local instance (r : Root) : AlgebraicGroup (rootSubgroup (k := k) r).carrierVariety :=
  (rootSubgroup (k := k) r).carrierAlgebraicGroup

omit [IsAlgClosed k] in
private lemma matrixN_inv (r : Root) (t : k) :
    (matrixN r t)⁻¹ = matrixN r t := by
  simp only [matrixN, mul_inv_rev, rootCurve_inv, CharTwo.neg_eq]
  group

/-- The GLS word is the inverse of the representation-coroot word. -/
lemma sourceWord_ambient (r : Root) (t : Variety.Point (KMult k)) :
    (ambientClosedCarrier (k := k)).inclusion.onPoints
      ((binaryCorootWord (rootMorphism r).toVariety
        (rootMorphism (-r)).toVariety).toFun t) =
      matrixToAmbient ((matrixH r (dPointEquiv 1 t 0 : k))⁻¹) := by
  have hroot (s : Root) (a : k) :
      (ambientClosedCarrier (k := k)).inclusion.onPoints
        ((rootMorphism s).toVariety.toFun (kPlusPoint a)) =
          matrixToAmbient (rootCurve s a) :=
    (rootMorphism_inclusion_apply s (kPlusPoint a)).trans (matrixToAmbient_root s a).symm
  rw [binaryCorootWord_apply]
  simp only [map_mul, map_inv, hroot]
  simp only [← map_inv, ← map_mul]
  apply congrArg matrixToAmbient
  change (rootCurve r 1 * rootCurve (-r) 1 * rootCurve r 1)⁻¹ *
    (rootCurve r _ * rootCurve (-r) _ * rootCurve r _) = _
  have hn1 : rootCurve (S := k) r 1 * rootCurve (-r) 1 * rootCurve r 1 = matrixN r 1 := by
    simp [matrixN, CharTwo.neg_eq]
  have hnt : rootCurve (S := k) r (dPointEquiv 1 t 0 : k) *
      rootCurve (-r) (dPointEquiv 1 t 0 : k)⁻¹ *
        rootCurve r (dPointEquiv 1 t 0 : k) = matrixN r (dPointEquiv 1 t 0 : k) := by
    simp [matrixN, CharTwo.neg_eq]
  rw [hn1, hnt, matrixH, CharTwo.neg_eq (1 : k), mul_inv_rev, matrixN_inv, matrixN_inv]

/-- On a simple root, the GLS word is the inverse of the existing simple cocharacter. -/
lemma sourceWord_simple (i : Fin 4) (t : Variety.Point (KMult k)) :
    (binaryCorootWord (rootMorphism (typeF4SimpleRootIndex i)).toVariety
      (rootMorphism (-(typeF4SimpleRootIndex i))).toVariety).toFun t =
      ((splitTorus (k := k)).inclusion.onPoints
        ((splitTorusSimpleCoroot i).onPoints t))⁻¹ := by
  apply (ambientClosedCarrier (k := k)).inclusion_injective
  rw [sourceWord_ambient]
  simp only [map_inv]
  exact congrArg Inv.inv (splitTorusSimpleCoroot_ambient_apply i t).symm

/-- The source-convention word of a literal simple pair belongs to the split torus. -/
lemma sourceWord_simple_mem (i : typeF4RootPairing_base.support)
    (t : Variety.Point (KMult k)) :
    (binaryCorootWord (rootMorphism i).toVariety
      (rootMorphism (-i : Root)).toVariety).toFun t ∈ splitTorus (k := k) := by
  obtain ⟨j, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
  rw [show (typeF4RootPairing_baseEquiv j : Root) = typeF4SimpleRootIndex j from rfl,
    sourceWord_simple]
  apply Subgroup.inv_mem
  exact ((splitTorus (k := k)).pointEquiv ((splitTorusSimpleCoroot j).onPoints t)).property

omit [CharP k 2] in
/-- The canonical parametrization recovers the literal ambient root morphism. -/
lemma rootParametrization_comp_inclusion (r : Root) :
    (rootSubgroup (k := k) r).inclusion.comp (rootParametrization r).hom =
      rootMorphism r := by
  apply Morphism.ext
  funext x
  change (rootSubgroup r).inclusion.onPoints
    ((rootParametrization (k := k) r).hom.onPoints x) = (rootMorphism r).onPoints x
  rw [rootParametrization_hom]
  exact Morphism.codRestrictClosedSubgroup_inclusion_apply (rootMorphism r)
    (rootSubgroup r) (fun y => ⟨y, rfl⟩) x

/-- Construct a simple-root chart from a compatible regular SL₂ morphism.
The literal coroot calculation supplies its diagonal containment. -/
noncomputable def simpleChart
    (i : typeF4RootPairing_base.support)
    (f : Morphism (slVariety k 2) (Carrier (k := k)))
    (hp : f.comp standardSL2UpperMorphism = rootMorphism i)
    (hm : f.comp standardSL2LowerMorphism = rootMorphism (-i : Root)) :
    BinaryOppositeRootSL2Chart (splitTorus (k := k)) (rootSubgroup i)
      (rootSubgroup (typeF4RootPairing.reflectionPerm i i)) := by
  have hn : typeF4RootPairing.reflectionPerm i i = (-i : Root) := rfl
  rw [hn]
  refine BinaryOppositeRootSL2Chart.ofAmbient _ _ _
    (rootParametrization i) (rootParametrization (-i : Root)) f ?_ ?_ ?_
  · rw [rootParametrization_comp_inclusion]
    exact hp
  · rw [rootParametrization_comp_inclusion]
    exact hm
  · intro t
    change f.onPoints ((binarySL2Coroot (k := k)).toVariety.toFun t) ∈ _
    rw [binarySL2Coroot_toVariety, binaryCorootWord_map]
    change
      (binaryCorootWord (f.comp standardSL2UpperMorphism).toVariety
        (f.comp standardSL2LowerMorphism).toVariety).toFun t ∈ _
    rw [hp, hm]
    exact sourceWord_simple_mem i t

end Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts
