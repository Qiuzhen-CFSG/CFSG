module
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.RootTable

/-!
# Native Weyl action on all positive triality roots

The finite signed D₄ root tables act on the actual Geck curves. Transport
through the injective carrier-to-split map gives the positive half of the
triality Weyl equations on `Standard.Carrier`. The simple roots change sign
through the pinned rank-one maps. The C,D equations retain F² and F; their
origin is the cyclic permutation of the three commuting split factors.

Every characteristic-two parameter, including q=2 and q=4, is covered.
The torus equations and the full abstract presentation comparison are separate.
Source: GLS3 2.4.4 and 2.4.8(e). The two local split calculations follow
`OuterOddSubgroups/Coverage/RootGeometry/Generation.lean` at their exact pinnings.
-/

@[expose] public noncomputable section

namespace Triality.Standard.RootPresentationRecognition.PositiveWeylModel
open Parabolics ConcreteBruhat PositiveCoordinates RadicalCoordinates.LeviCommutators
open Parabolics.RankOneMatrices PositiveCoordinates.SumExchangeData
open Theory.AlgebraicGroup.StandardRootSystem

private theorem conjugate_mul {G : Type*} [Group G] (g x y : G) :
    g * (x*y) * g⁻¹ = (g*x*g⁻¹) * (g*y*g⁻¹) := by group

private theorem simple_curve (P : Parameters) (hp : P.prime = 2)
    (a : Node) (i j : Fin 12)
    (h : (foldedRootReflection a).val (rootIndex i) = rootIndex j)
    (t : ExtensionField P) :
    elementaryInclusion P (simpleElementary P hp a) * curve P i t *
      (elementaryInclusion P (simpleElementary P hp a))⁻¹ = curve P j t := by
  let D := InputRealization.inputs P hp
  have hn : D.lift (foldedRootReflection a) = elementaryInclusion P (simpleElementary P hp a) := by
    cases a
    · simp only [foldedRootReflection,map_mul,SplitNormalForm.Inputs.lift_simple,
        elementaryInclusion_simple_arms]
    · simp only [foldedRootReflection,SplitNormalForm.Inputs.lift_simple,
        elementaryInclusion_simple_central]
  have hc := D.conjugate_root (foldedRootReflection a) (rootIndex i) t
  exact (congrArg (fun n : SplitGroup P => n * curve P i t * n⁻¹) hn.symm).trans
    (hc.trans (congrArg (fun r => SplitNormalForm.rootCurve P r t) h))

/-- A,B are the same native simple roots used to define the Weyl words. -/
theorem short_zero (P : Parameters) (hp : P.prime = 2) (t : ExtensionField P) :
    short P hp 0 t = ConcreteBruhat.rootElement P hp true .arms t := by
  have hc : shortSplit P 0 t = elementaryInclusion P (rootElementary P hp true .arms t) :=
    congrArg₂ (· * ·)
      (congrArg₂ (· * ·) (curve_simple P 0 t) (curve_simple P 2 (fieldFrobenius P t)))
      (curve_simple P 3 (fieldFrobenius P (fieldFrobenius P t)))
  exact congrArg (toCarrier P) (elementaryInclusion_injective P
    ((shortElementary_val P hp 0 t).trans hc))

theorem long_zero (P : Parameters) (hp : P.prime = 2) (t : fixedField P) :
    long P hp 0 t = ConcreteBruhat.rootElement P hp true .central t := by
  have hc : longSplit P 0 t = elementaryInclusion P (rootElementary P hp true .central t) :=
    curve_simple P 1 t.val
  exact congrArg (toCarrier P) (elementaryInclusion_injective P
    ((longElementary_val P hp 0 t).trans hc))

private theorem representative_inv (P : Parameters) (hp : P.prime = 2) (a : Node) :
    (simpleRepresentative P hp a)⁻¹ = simpleRepresentative P hp a :=
  inv_eq_of_mul_eq_one_left ((pow_two _).symm.trans (simpleRepresentative_sq P hp a))

/-- The two simple positive roots change sign with their original parameters. -/
theorem arms_short_zero (P : Parameters) (hp : P.prime = 2) (t : ExtensionField P) :
    simpleRepresentative P hp .arms * short P hp 0 t * (simpleRepresentative P hp .arms)⁻¹ =
      ConcreteBruhat.rootElement P hp false .arms t := by
  rw [short_zero,representative_inv,simpleRepresentative_positive]

theorem central_long_zero (P : Parameters) (hp : P.prime = 2) (t : fixedField P) :
    simpleRepresentative P hp .central * long P hp 0 t * (simpleRepresentative P hp .central)⁻¹ =
      ConcreteBruhat.rootElement P hp false .central t := by
  rw [long_zero,representative_inv,simpleRepresentative_positive]

/-- All three short positive roots under the central reflection. -/
theorem central_short (P : Parameters) (hp : P.prime = 2) (i : Fin 3) (t : ExtensionField P) :
    simpleRepresentative P hp .central * short P hp i t * (simpleRepresentative P hp .central)⁻¹ =
      short P hp (![1,0,2] i) t := by
  have ht (j : Fin 3) :
      (foldedRootReflection .central).val (rootIndex (shortPosition i j)) =
        rootIndex (shortPosition (![1,0,2] i) j) := by
    simpa only [RootTable.signedIndex,if_true,rootEnumeration_positiveIndex]
      using RootTable.central_short true i j
  apply FixedDescent.carrierToSplit_injective P hp
  simp only [map_mul,map_inv,simpleRepresentative,short,FixedDescent.carrierToSplit_toCarrier,
    shortElementary_val,shortSplit,conjugate_mul,simple_curve P hp .central _ _ (ht _)]

/-- All three long positive roots under the arm reflection. -/
theorem arms_long (P : Parameters) (hp : P.prime = 2) (i : Fin 3) (t : fixedField P) :
    simpleRepresentative P hp .arms * long P hp i t * (simpleRepresentative P hp .arms)⁻¹ =
      long P hp (![1,0,2] i) t := by
  have ht : (foldedRootReflection .arms).val (rootIndex (longPosition i)) =
      rootIndex (longPosition (![1,0,2] i)) := by
    simpa only [RootTable.signedIndex,if_true,rootEnumeration_positiveIndex]
      using RootTable.arms_long true i
  apply FixedDescent.carrierToSplit_injective P hp
  simp only [map_mul,map_inv,simpleRepresentative,long,FixedDescent.carrierToSplit_toCarrier,
    longElementary_val,longSplit,simple_curve P hp .arms _ _ ht]

/-- The central reflection interchanges E,F and does not change fixed-field scalars. -/
theorem central_long (P : Parameters) (hp : P.prime = 2) (i : Fin 3) (hi : i ≠ 0)
    (t : fixedField P) :
    simpleRepresentative P hp .central * long P hp i t * (simpleRepresentative P hp .central)⁻¹ =
      long P hp (![0,2,1] i) t := by
  have ht : (foldedRootReflection .central).val (rootIndex (longPosition i)) =
      rootIndex (longPosition (![0,2,1] i)) := by
    simpa only [RootTable.centralLongTarget,hi,if_false,RootTable.signedIndex,if_true,
      rootEnumeration_positiveIndex] using RootTable.central_long true i
  apply FixedDescent.carrierToSplit_injective P hp
  simp only [map_mul,map_inv,simpleRepresentative,long,FixedDescent.carrierToSplit_toCarrier,
    longElementary_val,longSplit,simple_curve P hp .central _ _ ht]

/-- C(s) goes to D(F²(s)); the shift follows from the actual split root table. -/
theorem arms_short_one (P : Parameters) (hp : P.prime = 2) (t : ExtensionField P) :
    simpleRepresentative P hp .arms * short P hp 1 t * (simpleRepresentative P hp .arms)⁻¹ =
      short P hp 2 (fieldFrobenius P (fieldFrobenius P t)) := by
  have ht (j : Fin 3) : (foldedRootReflection .arms).val (rootIndex (shortPosition 1 j)) =
      rootIndex (shortPosition 2 (j+1)) := by
    simpa [RootTable.armShortTarget,RootTable.signedIndex,rootEnumeration_positiveIndex]
      using RootTable.arms_short true 1 j
  apply FixedDescent.carrierToSplit_injective P hp
  simp only [map_mul,map_inv,simpleRepresentative,short,FixedDescent.carrierToSplit_toCarrier,
    shortElementary_val,shortSplit,conjugate_mul,simple_curve P hp .arms _ _ (ht _),
    fieldFrobenius_three]
  change curve P 8 t * curve P 9 (fieldFrobenius P t) * curve P 7 (fieldFrobenius P (fieldFrobenius P t)) =
    curve P 7 (fieldFrobenius P (fieldFrobenius P t)) * curve P 8 t * curve P 9 (fieldFrobenius P t)
  have h78 := curve_diagram_commute P 7 (fieldFrobenius P (fieldFrobenius P t)) t
  have h97 := curve_diagram_commute P 9 (fieldFrobenius P t) (fieldFrobenius P (fieldFrobenius P t))
  change Commute (curve P 7 _) (curve P 8 _) at h78
  change Commute (curve P 9 _) (curve P 7 _) at h97
  rw [← (h78.mul_right h97.symm).eq,mul_assoc]

/-- D(s) goes back to C(F(s)), on the same native carrier. -/
theorem arms_short_two (P : Parameters) (hp : P.prime = 2) (t : ExtensionField P) :
    simpleRepresentative P hp .arms * short P hp 2 t * (simpleRepresentative P hp .arms)⁻¹ =
      short P hp 1 (fieldFrobenius P t) := by
  have h := arms_short_one P hp (fieldFrobenius P t)
  rw [fieldFrobenius_three] at h
  rw [← h]
  have hs : simpleRepresentative P hp .arms * simpleRepresentative P hp .arms = 1 :=
    (pow_two _).symm.trans (simpleRepresentative_sq P hp .arms)
  rw [representative_inv]
  simp only [← mul_assoc,hs,one_mul]
  rw [mul_assoc,hs,mul_one]

end Triality.Standard.RootPresentationRecognition.PositiveWeylModel
