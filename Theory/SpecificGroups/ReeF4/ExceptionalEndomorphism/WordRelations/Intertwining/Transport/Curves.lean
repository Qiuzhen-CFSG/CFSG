module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.WeylDuality
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4IntegralChevalleyRepresentation
public import Theory.AlgebraicGroup.RootSystems.IntegralRootCurveSimpleGeneration
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.RouteComparison

/-!
# Canonical F4 root curves and exceptional dual routes

A positive canonical curve is the Tits conjugate of its route's positive simple
curve, while the opposite curve uses the negative simple curve along the same
route. These identities hold over every commutative ring. In characteristic
two, the integral operator comparison in `RouteComparison` identifies the
curves obtained from any two routes to the same root.

Exceptional duality reverses each simple generator of a route. Applying the
operator comparison to this reversed route and the independently chosen route
to the dual root proves the dual-curve formulas for both signs. Weyl invariance
of root length also preserves the exceptional parameter exponent. These are
unconditional identities for `F4Chevalley.rootCurve`, not an assumption of the
all-root exceptional intertwiner.

The integral normalization is that of `IntegralAllRootOperators` and
`IntegralChevalleyRootCurves`, following Steinberg, *Lectures on Chevalley
Groups*. The exceptional duality convention is the one used in `RootDuality`
(Aschbacher–Smith, Remark A.2.4).
-/

public section

namespace ReeF4.WordRelations

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Classical Matrix

noncomputable local instance : Fintype typeF4Roots := Fintype.ofFinite _

noncomputable section

/-- Reversing every simple generator intertwines the action on all roots. -/
theorem exceptionalRootPermutation_reflectionWord
    (word : List typeF4RootPairing_base.support) (r : typeF4Roots) :
    exceptionalRootPermutation (reflectionWord (P := typeF4RootPairing) word r) =
      reflectionWord (P := typeF4RootPairing) (word.map simplePermutation)
        (exceptionalRootPermutation r) := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    simp only [reflectionWord, List.map_cons, exceptionalRootPermutation_reflection, ih,
      simplePermutation_val]

/-- The reversed canonical route reaches the dual root; it need not be the
canonical route chosen for that dual root. -/
theorem dual_rootRoute_target (r : typeF4Roots) :
    reflectionWord (P := typeF4RootPairing)
        ((rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).word.map
          simplePermutation)
        (simplePermutation
          (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).simple) =
      exceptionalRootPermutation r := by
  rw [simplePermutation_val, ← exceptionalRootPermutation_reflectionWord,
    (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).target]

/-- The same endpoint calculation on the actual root coordinates. -/
theorem coordinatePermutation_reflectionWord
    (word : List typeF4RootPairing_base.support) (r : typeF4Roots) :
    coordinatePermutation (Sum.inr (reflectionWord (P := typeF4RootPairing) word r)) =
      Sum.inr (reflectionWord (P := typeF4RootPairing) (word.map simplePermutation)
        (exceptionalRootPermutation r)) := by
  rw [coordinatePermutation_inr, exceptionalRootPermutation_reflectionWord]

/-- The integral Tits word specialized to a unit over the coefficient ring. -/
@[expose] def titsUnit {S : Type*} [CommRing S]
    (word : List typeF4RootPairing_base.support) :
    (Matrix Coordinate Coordinate S)ˣ :=
  rootCurveTitsWord (P := typeF4RootPairing) word

@[simp] theorem titsUnit_val {S : Type*} [CommRing S]
    (word : List typeF4RootPairing_base.support) :
    (titsUnit (S := S) word).val =
      specializeMatrix (titsWord (P := typeF4RootPairing) word) := rfl

@[simp] theorem titsUnit_inv_val {S : Type*} [CommRing S]
    (word : List typeF4RootPairing_base.support) :
    ((titsUnit (S := S) word)⁻¹).val =
      specializeMatrix (titsWordInv (P := typeF4RootPairing) word) := rfl

@[simp] theorem titsUnit_nil {S : Type*} [CommRing S] :
    titsUnit (S := S) [] = 1 := rootCurveTitsWord_nil

/-- Each Tits generator is the product of the actual signed simple root curves,
with the integral convention `x_i(1) x_{-i}(-1) x_i(1)`. -/
theorem titsUnit_cons {S : Type*} [CommRing S]
    (i : typeF4RootPairing_base.support) (word : List typeF4RootPairing_base.support) :
    letI := typeF4RootPairing.indexNeg
    titsUnit (S := S) (i :: word) =
      F4Chevalley.rootCurve i.val 1 * F4Chevalley.rootCurve (-i.val) (-1) *
        F4Chevalley.rootCurve i.val 1 * titsUnit word := by
  let := typeF4RootPairing.indexNeg
  change rootCurveTitsWord (P := typeF4RootPairing) (i :: word) =
    rootCurveUnit integralChevalleyRootOperators i.val (1 : S) *
      rootCurveUnit integralChevalleyRootOperators (-i.val) (-1) *
      rootCurveUnit integralChevalleyRootOperators i.val 1 * rootCurveTitsWord word
  rw [rootCurveUnit_simple, rootCurveUnit_neg_simple]
  exact rootCurveTitsWord_cons i word

private theorem dividedPower_simple (i : typeF4RootPairing_base.support) (n : ℕ) :
    F4Chevalley.integralOperators.rootDividedPower i n =
      eDividedPower (P := typeF4RootPairing) i n := by
  change rootDividedPower (P := typeF4RootPairing) (b := typeF4RootPairing_base) i n = _
  rw [rootDividedPower_of_pos (i : typeF4Roots) (typeF4RootPairing_base.isPos_of_mem_support i.property)]
  simp only [rootRoute_word_simple, rootRoute_simple, transportedMatrix_nil]

private theorem dividedPower_neg_simple (i : typeF4RootPairing_base.support) (n : ℕ) :
    letI := typeF4RootPairing.indexNeg
    F4Chevalley.integralOperators.rootDividedPower (-i) n =
      fDividedPower (P := typeF4RootPairing) i n := by
  let _ := typeF4RootPairing.indexNeg
  change rootDividedPower (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-i) n = _
  rw [rootDividedPower_neg_of_pos (i : typeF4Roots) (typeF4RootPairing_base.isPos_of_mem_support i.property)]
  simp only [rootRoute_word_simple, rootRoute_simple, transportedMatrix_nil]

/-- The actual positive canonical curve is the conjugate of its route's
positive simple curve, over every commutative ring. -/
theorem rootCurve_of_pos_route {S : Type*} [CommRing S]
    (r : typeF4Roots) (hr : typeF4RootPairing_base.IsPos r) (t : S) :
    F4Chevalley.rootCurve r t =
      titsUnit (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).word *
        F4Chevalley.rootCurve
          (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).simple t *
        (titsUnit (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).word)⁻¹ := by
  apply Units.ext
  simp only [Units.val_mul, F4Chevalley.rootCurve_matrix_formula, dividedPower_simple]
  change 1 + t • specializeMatrix (rootDividedPower (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) r 1) +
    t ^ 2 • specializeMatrix (rootDividedPower (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) r 2) +
    t ^ 3 • specializeMatrix (rootDividedPower (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) r 3) = _
  rw [rootDividedPower_of_pos r hr, rootDividedPower_of_pos r hr,
    rootDividedPower_of_pos r hr]
  simp only [specializeMatrix_transportedMatrix, titsUnit_val, titsUnit_inv_val,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one]
  have hTI := (titsUnit (S := S)
    (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).word).val_inv
  exact congrArg (fun A => A + t • _ + t ^ 2 • _ + t ^ 3 • _) hTI.symm

/-- Opposite roots share the positive route, transporting its negative simple
curve rather than choosing a new normalization. -/
theorem rootCurve_neg_of_pos_route {S : Type*} [CommRing S]
    (r : typeF4Roots) (hr : typeF4RootPairing_base.IsPos r) (t : S) :
    letI := typeF4RootPairing.indexNeg
    F4Chevalley.rootCurve (-r) t =
      titsUnit (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).word *
        F4Chevalley.rootCurve
          (-(rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).simple) t *
        (titsUnit (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).word)⁻¹ := by
  let _ := typeF4RootPairing.indexNeg
  apply Units.ext
  simp only [Units.val_mul, F4Chevalley.rootCurve_matrix_formula, dividedPower_neg_simple]
  change 1 + t • specializeMatrix (rootDividedPower (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) (-r) 1) +
    t ^ 2 • specializeMatrix (rootDividedPower (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) (-r) 2) +
    t ^ 3 • specializeMatrix (rootDividedPower (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) (-r) 3) = _
  rw [rootDividedPower_neg_of_pos r hr, rootDividedPower_neg_of_pos r hr,
    rootDividedPower_neg_of_pos r hr]
  simp only [specializeMatrix_transportedMatrix, titsUnit_val, titsUnit_inv_val,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one]
  have hTI := (titsUnit (S := S)
    (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).word).val_inv
  exact congrArg (fun A => A + t • _ + t ^ 2 • _ + t ^ 3 • _) hTI.symm


/-- Any route to a positive root gives its actual specialized divided powers
in characteristic two, including routes with a different simple source. -/
theorem rootDividedPower_of_pos_transport {S : Type*} [CommRing S] [CharP S 2]
    (r : typeF4Roots) (hr : typeF4RootPairing_base.IsPos r)
    (word : List typeF4RootPairing_base.support) (i : typeF4RootPairing_base.support)
    (hroot : reflectionWord (P := typeF4RootPairing) word i = r) (n : ℕ) :
    specializeMatrix (S := S) (F4Chevalley.integralOperators.rootDividedPower r n) =
      specializeMatrix (transportedMatrix word (eDividedPower i n)) := by
  change specializeMatrix (rootDividedPower (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) r n) = _
  rw [rootDividedPower_of_pos r hr]
  apply RouteComparison.specialize_transported_eDividedPower_eq
  exact (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).target.trans
    hroot.symm

/-- The same comparison for the negative divided powers, using the route to
the positive opposite root, as in the integral normalization. -/
theorem rootDividedPower_neg_of_pos_transport {S : Type*} [CommRing S] [CharP S 2]
    (r : typeF4Roots) (hr : typeF4RootPairing_base.IsPos r)
    (word : List typeF4RootPairing_base.support) (i : typeF4RootPairing_base.support)
    (hroot : reflectionWord (P := typeF4RootPairing) word i = r) (n : ℕ) :
    letI := typeF4RootPairing.indexNeg
    specializeMatrix (S := S) (F4Chevalley.integralOperators.rootDividedPower (-r) n) =
      specializeMatrix (transportedMatrix word (fDividedPower i n)) := by
  let := typeF4RootPairing.indexNeg
  change specializeMatrix (rootDividedPower (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) (-r) n) = _
  rw [rootDividedPower_neg_of_pos r hr]
  apply RouteComparison.specialize_transported_fDividedPower_eq
  exact (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).target.trans
    hroot.symm

/-- The actual positive curve can be transported along any route to its root
in characteristic two. No comparison of chosen Weyl elements is required. -/
theorem rootCurve_of_pos_transport {S : Type*} [CommRing S] [CharP S 2]
    (r : typeF4Roots) (hr : typeF4RootPairing_base.IsPos r)
    (word : List typeF4RootPairing_base.support) (i : typeF4RootPairing_base.support)
    (hroot : reflectionWord (P := typeF4RootPairing) word i = r) (t : S) :
    F4Chevalley.rootCurve r t =
      titsUnit word * F4Chevalley.rootCurve i.val t * (titsUnit word)⁻¹ := by
  apply Units.ext
  simp only [Units.val_mul, F4Chevalley.rootCurve_matrix_formula, dividedPower_simple,
    rootDividedPower_of_pos_transport r hr word i hroot,
    specializeMatrix_transportedMatrix, titsUnit_val, titsUnit_inv_val,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  exact congrArg (fun A => A + t • _ + t ^ 2 • _ + t ^ 3 • _)
    (titsUnit (S := S) word).val_inv.symm

/-- The negative curve uses the negative simple curve along any route to the
positive opposite root, with all integral signs eliminated by characteristic two. -/
theorem rootCurve_neg_of_pos_transport {S : Type*} [CommRing S] [CharP S 2]
    (r : typeF4Roots) (hr : typeF4RootPairing_base.IsPos r)
    (word : List typeF4RootPairing_base.support) (i : typeF4RootPairing_base.support)
    (hroot : reflectionWord (P := typeF4RootPairing) word i = r) (t : S) :
    letI := typeF4RootPairing.indexNeg
    F4Chevalley.rootCurve (-r) t =
      titsUnit word * F4Chevalley.rootCurve (-i.val) t * (titsUnit word)⁻¹ := by
  let := typeF4RootPairing.indexNeg
  apply Units.ext
  simp only [Units.val_mul, F4Chevalley.rootCurve_matrix_formula, dividedPower_neg_simple,
    rootDividedPower_neg_of_pos_transport r hr word i hroot,
    specializeMatrix_transportedMatrix, titsUnit_val, titsUnit_inv_val,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  exact congrArg (fun A => A + t • _ + t ^ 2 • _ + t ^ 3 • _)
    (titsUnit (S := S) word).val_inv.symm

/-- The dual curve follows the reversed route of the original positive root.
The independently chosen canonical route to the dual has been compared at the
level of the actual divided-power operators. -/
theorem rootCurve_dual_of_pos_route {S : Type*} [CommRing S] [CharP S 2]
    (r : typeF4Roots) (hr : typeF4RootPairing_base.IsPos r) (t : S) :
    F4Chevalley.rootCurve (exceptionalRootPermutation r) t =
      titsUnit ((rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).word.map
        simplePermutation) *
      F4Chevalley.rootCurve
        (simplePermutation (rootRoute (P := typeF4RootPairing)
          (b := typeF4RootPairing_base) r).simple).val t *
      (titsUnit ((rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).word.map
        simplePermutation))⁻¹ :=
  rootCurve_of_pos_transport _ ((exceptionalRootPermutation_isPos r).mpr hr)
    _ _ (dual_rootRoute_target r) t

/-- The dual of a negative curve follows the reversed route to its positive
opposite and starts at the reversed negative simple root. -/
theorem rootCurve_dual_neg_of_pos_route {S : Type*} [CommRing S] [CharP S 2]
    (r : typeF4Roots) (hr : typeF4RootPairing_base.IsPos r) (t : S) :
    letI := typeF4RootPairing.indexNeg
    F4Chevalley.rootCurve (exceptionalRootPermutation (-r)) t =
      titsUnit ((rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).word.map
        simplePermutation) *
      F4Chevalley.rootCurve
        (-(simplePermutation (rootRoute (P := typeF4RootPairing)
          (b := typeF4RootPairing_base) r).simple).val) t *
      (titsUnit ((rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).word.map
        simplePermutation))⁻¹ := by
  let := typeF4RootPairing.indexNeg
  rw [exceptionalRootPermutation_neg]
  exact rootCurve_neg_of_pos_transport _ ((exceptionalRootPermutation_isPos r).mpr hr)
    _ _ (dual_rootRoute_target r) t


/-- Weyl reflections preserve the geometric long-root class. -/
theorem isLongRoot_reflection_iff (i r : typeF4Roots) :
    IsLongRoot (typeF4RootPairing.reflectionPerm i r) ↔ IsLongRoot r := by
  rw [isLongRoot_iff_shortIndex, isLongRoot_iff_shortIndex,
    RootPairing.isShortIndex_iff, RootPairing.isShortIndex_iff]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨typeF4RootPairing.reflectionPerm i s, ?_⟩
    simpa only [typeF4RootPairing.pairingIn_reflectionPerm,
      typeF4RootPairing.reflectionPerm_self] using hs
  · rintro ⟨s, hs⟩
    refine ⟨typeF4RootPairing.reflectionPerm i s, ?_⟩
    simpa only [typeF4RootPairing.pairingIn_reflectionPerm,
      typeF4RootPairing.reflectionPerm_self] using hs

/-- The exceptional parameter exponent is unchanged along a Weyl route. -/
theorem exceptionalParameter_reflectionWord {S : Type*} [Monoid S]
    (word : List typeF4RootPairing_base.support) (r : typeF4Roots) (t : S) :
    exceptionalParameter (reflectionWord (P := typeF4RootPairing) word r) t =
      exceptionalParameter r t := by
  have hlength : IsLongRoot (reflectionWord (P := typeF4RootPairing) word r) ↔
      IsLongRoot r := by
    induction word with
    | nil => rfl
    | cons i word ih => exact (isLongRoot_reflection_iff i.val _).trans ih
  by_cases hr : IsLongRoot r
  · rw [exceptionalParameter_of_long hr, exceptionalParameter_of_long (hlength.mpr hr)]
  · rw [exceptionalParameter_of_short hr,
      exceptionalParameter_of_short (fun h => hr (hlength.mp h))]

/-- The route's source simple root has exactly the target's exceptional parameter. -/
theorem exceptionalParameter_rootRoute {S : Type*} [Monoid S]
    (r : typeF4Roots) (t : S) :
    exceptionalParameter (rootRoute (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) r).simple.val t = exceptionalParameter r t := by
  let route := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  exact (exceptionalParameter_reflectionWord route.word route.simple t).symm.trans
    (congrArg (fun s => exceptionalParameter s t) route.target)

end
end ReeF4.WordRelations
