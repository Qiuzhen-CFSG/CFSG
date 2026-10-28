module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Ambient.Comparison
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Ambient.Calculation

/-!
# Lifting the full 52-dimensional Suzuki calculation

`Ambient.Comparison` proves the full simple-root matrix comparison for every
Ree coefficient field. Simple Weyl conjugation extends it to the high and mixed
roots of the Suzuki word. Multiplication then identifies the exact panel Weyl
word and the two prescribed coroot factors, without torus or parabolic inputs.

Consequently the finite matrix predicate `GaussIdentity m` implies the literal
`SplitIdentity m`. Only subgroup and unit coercions are discarded, so their
injectivity proves equality in the actual split group. The full-coordinate
Gauss calculation is still required; this module does not assert it.

Source: GLS3 2.3.8 and Table 2.4 type V,
`refs/KGroup/GLS3/chapter2.tex`, using the actual integral Geck root curves.
-/

public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient
open BlockParameters.FieldRecovery Parabolics
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
variable {m : ℕ}
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private def splitMatrix : SplitGroup m →* MatrixCarrier m :=
  (Units.coeHom _).comp (SplitGroup m).subtype

private theorem splitMatrix_injective : Function.Injective (splitMatrix (m := m)) :=
  Units.val_injective.comp Subtype.val_injective

private theorem weyl_comparison (h : SimpleComparison m) (i : Fin 2)
    (t : CoefficientField m) :
    splitMatrix (weylWord m (typeF4SimpleRootIndex (if i = 0 then 1 else 2)) t) =
      fullMatrixEquiv m (weylMatrix i t) := by
  have hp (a : CoefficientField m) :
      splitMatrix (rootGeneratorInGroup m
        (typeF4SimpleRootIndex (if i = 0 then 1 else 2)) a) =
        fullMatrixEquiv m (simpleMatrix true i a) := h true i a
  have hn (a : CoefficientField m) :
      splitMatrix (rootGeneratorInGroup m
        (-(typeF4SimpleRootIndex (if i = 0 then 1 else 2))) a) =
        fullMatrixEquiv m (simpleMatrix false i a) := h false i a
  simp only [weylWord, map_mul, CharTwo.neg_eq, hp, hn, weylMatrix]

private theorem root_inv (r : F4Chevalley.Root) (t : CoefficientField m) :
    (rootGeneratorInGroup m r t)⁻¹ = rootGeneratorInGroup m r t := by
  apply Subtype.ext
  simp [F4Chevalley.rootCurve_inv, CharTwo.neg_eq]

private theorem weyl_one_inv (i : Fin 4) :
    (weylWord m (typeF4SimpleRootIndex i) 1)⁻¹ =
      weylWord m (typeF4SimpleRootIndex i) 1 := by
  simp only [weylWord, mul_inv_rev, root_inv, mul_assoc]

private theorem simple_weyl_conj (i : Fin 4) (r : F4Chevalley.Root) (t : CoefficientField m) :
    weylWord m (typeF4SimpleRootIndex i) 1 * rootGeneratorInGroup m r t *
      (weylWord m (typeF4SimpleRootIndex i) 1)⁻¹ =
      rootGeneratorInGroup m (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) t := by
  apply Subtype.ext
  have hw : (weylWord m (typeF4SimpleRootIndex i) 1).val =
      ReeF4.WordRelations.titsUnit [typeF4RootPairing_baseEquiv i] := by
    simp [weylWord, ReeF4.WordRelations.titsUnit_cons, ReeF4.WordRelations.titsUnit_nil,
      typeF4RootPairing_baseEquiv_val]
  change (weylWord m (typeF4SimpleRootIndex i) 1).val * F4Chevalley.rootCurve r t *
    ((weylWord m (typeF4SimpleRootIndex i) 1).val)⁻¹ = _
  rw [hw]
  exact PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport.simple_conj
    (typeF4RootPairing_baseEquiv i) r t

private theorem root_neg (r : F4Chevalley.Root) :
    typeF4RootPairing.root (-r) = -typeF4RootPairing.root r := by
  rw [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_self]

private theorem reflection_signed (p : Bool) (r s : F4Chevalley.Root) :
    typeF4RootPairing.reflectionPerm r (signedRoot p s) =
      signedRoot p (typeF4RootPairing.reflectionPerm r s) := by
  apply typeF4RootPairing.root.injective
  cases p
  · change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm r (-s)) =
      typeF4RootPairing.root (-(typeF4RootPairing.reflectionPerm r s))
    rw [RootPairing.root_reflectionPerm, root_neg, root_neg,
      RootPairing.root_reflectionPerm, map_neg]
  · rfl

private theorem reflected_comparison (h : SimpleComparison m) (p : Bool) (i j : Fin 2)
    (t : CoefficientField m) :
    splitMatrix (rootGeneratorInGroup m
      (signedRoot p (typeF4RootPairing.reflectionPerm
        (typeF4SimpleRootIndex (if i = 0 then 1 else 2))
        (typeF4SimpleRootIndex (if j = 0 then 1 else 2)))) t) =
      fullMatrixEquiv m (reflectionMatrix i * simpleMatrix p j t * reflectionMatrix i) := by
  rw [← reflection_signed, ← simple_weyl_conj, weyl_one_inv]
  simp only [map_mul, weyl_comparison h]
  have hs : splitMatrix (rootGeneratorInGroup m
      (signedRoot p (typeF4SimpleRootIndex (if j = 0 then 1 else 2))) t) =
      fullMatrixEquiv m (simpleMatrix p j t) := h p j t
  rw [hs]
  rfl

/-- Four full simple-root comparisons imply the comparisons for all eight signed B₂ roots. -/
theorem root_comparison (h : SimpleComparison m) (p : Bool) (i : Fin 4)
    (t : CoefficientField m) :
    (F4Chevalley.rootCurve (suzukiRoots p i) t).val =
      fullMatrixEquiv m (rootMatrix p i t) := by
  fin_cases i
  · exact h p 0 t
  · exact h p 1 t
  · exact reflected_comparison h p 1 0 t
  · exact reflected_comparison h p 0 1 t

private theorem word_comparison (h : SimpleComparison m) (p : Bool)
    (t u : CoefficientField m) :
    splitMatrix (suzukiWord m p t u) = fullMatrixEquiv m (wordMatrix p t u) := by
  have hr (i : Fin 4) (a : CoefficientField m) :
      splitMatrix (rootGeneratorInGroup m (suzukiRoots p i) a) =
        fullMatrixEquiv m (rootMatrix p i a) := root_comparison h p i a
  simp only [suzukiWord, wordMatrix, map_mul, hr]

private theorem panel_comparison (h : SimpleComparison m) :
    splitMatrix (Binary.FixedGeometry.simpleWord m [1,2,1,2]) =
      fullMatrixEquiv m panelMatrix := by
  simp only [Binary.FixedGeometry.simpleWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, map_mul]
  have h0 := weyl_comparison h 0 1
  have h1 := weyl_comparison h 1 1
  simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq] at h0 h1
  rw [h0, h1]
  simp only [panelMatrix, reflectionMatrix, map_mul, mul_assoc]

private theorem torus_comparison (h : SimpleComparison m) (n : (CoefficientField m)ˣ) :
    splitMatrix (torusFactor n) = fullMatrixEquiv m (torusMatrix n) := by
  simp only [torusFactor, torusWord, map_mul, CharTwo.neg_eq]
  have h0 := weyl_comparison h 0
  have h1 := weyl_comparison h 1
  simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq] at h0 h1
  rw [h0, h0, h1, h1]
  simp only [torusMatrix, reflectionMatrix, map_mul, Units.coe_map]
  rfl

/-- The finite full-matrix equation and four genuine generator comparisons
suffice for the literal equation in `SplitGroup m`. Both premises remain
separate proof obligations until instantiated. -/
theorem splitIdentity_of_comparison (h : SimpleComparison m) (hg : GaussIdentity m) :
    SplitIdentity m := by
  intro t u hn
  apply splitMatrix_injective
  simp only [map_mul, panel_comparison h, word_comparison h, torus_comparison h]
  simpa only [map_mul] using congrArg (fullMatrixEquiv m) (hg t u hn)

/-- With the full simple-root comparison discharged, only the explicit
52-dimensional matrix calculation remains. -/
theorem splitIdentity_of_gauss (m : ℕ) (hg : GaussIdentity m) : SplitIdentity m :=
  splitIdentity_of_comparison (simpleComparison m) hg

/-- The literal split-root Suzuki Gauss identity on the full Ree carrier. -/
theorem splitIdentity (m : ℕ) : SplitIdentity m :=
  splitIdentity_of_gauss m (gaussIdentity m)

end ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient
