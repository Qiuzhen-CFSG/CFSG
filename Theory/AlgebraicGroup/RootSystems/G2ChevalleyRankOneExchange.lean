module

public import Theory.AlgebraicGroup.RootSystems.G2ChevalleyWeylLifts

/-!
# Characteristic-free rank-one exchange for the G2 Chevalley carrier

This module proves the pointwise opposite-root exchange used to collect words
in the explicit G2 Chevalley carrier.  For every one of the twelve roots, the
nonsingular branch factors `x_r(a) x_{-r}(b)` as a negative-root point, the
coroot point in the rank-two split torus `dVariety k 2`, and a positive-root
point.  When `a * b = 1`, the singular branch instead ends in a certified Weyl
representative, with a separately certified inverse.

The two simple-root identities are checked entrywise in the fourteen-dimensional
integral Chevalley representation.  Multiplication by the diagonal torus is
first reduced entrywise, leaving polynomial identities over an arbitrary field;
no division by 2 or 3 occurs.  Explicit short- and long-root Weyl words then
transport those identities to all roots while preserving the root parameters
and producing the displayed coroot coordinates.  Thus the formulas remain valid
in characteristics 2 and 3.

This is the local rank-one input for the finite explicit Bruhat cover.  Its only
project dependency is the axiom-clean chain through `G2ChevalleyWeylLifts`,
ultimately using the representation, carrier, and root-curve modules.  The
construction follows the standard rank-one Chevalley factorization in
Steinberg, *Lectures on Chevalley Groups*, together with the chosen integral G2
root-vector normalization; it does not use torus-root exhaustiveness, root
realization, semisimplicity, or center calculations.
-/

open scoped Matrix

open Theory AlgebraicGroup

namespace Theory.AlgebraicGroup.G2Chevalley

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Rational points of the closed G2 Chevalley carrier. -/
public abbrev CarrierPoint :=
  Variety.Point (Carrier (k := k))

/-- Coordinates of the coroot of `r` in the short and long simple-coroot basis. -/
@[expose] public def rootCorootTorusParameter {R : Type*} [CommRing R]
    (r : Root) (c : Rˣ) : TorusParameter R :=
  match r with
  | 0 => ![c, 1]
  | 1 => ![1, c]
  | 2 => ![c, c ^ 3]
  | 3 => ![c ^ 2, c ^ 3]
  | 4 => ![c, c]
  | 5 => ![c, c ^ 2]
  | 6 => ![c⁻¹, 1]
  | 7 => ![1, c⁻¹]
  | 8 => ![c⁻¹, c⁻¹ ^ 3]
  | 9 => ![c⁻¹ ^ 2, c⁻¹ ^ 3]
  | 10 => ![c⁻¹, c⁻¹]
  | 11 => ![c⁻¹, c⁻¹ ^ 2]

/-- The rank-two split-torus point with coordinates `rootCorootTorusParameter r c`. -/
@[expose] public noncomputable def rootCorootTorusPoint (r : Root) (c : kˣ) :
    Variety.Point (dVariety k 2) :=
  (dPointEquiv 2).symm (rootCorootTorusParameter r c)

/-- The coroot point embedded in the closed G2 carrier. -/
@[expose] public noncomputable def rootCorootTorusFactor (r : Root) (c : kˣ) :
    CarrierPoint (k := k) :=
  (splitTorusMorphism (k := k)).onPoints (rootCorootTorusPoint r c)

omit [IsAlgClosed k] in
/-- Applying the standard point equivalence recovers the displayed coroot coordinates. -/
public theorem rootCorootTorusPoint_coordinates (r : Root) (c : kˣ) :
    dPointEquiv 2 (rootCorootTorusPoint (k := k) r c) =
      rootCorootTorusParameter r c := by
  exact (dPointEquiv 2).apply_symm_apply _

private def simpleCorootTorusParameter {R : Type*} [CommRing R]
    (i : Fin 2) (c : Rˣ) : TorusParameter R :=
  match i with
  | 0 => ![c, 1]
  | 1 => ![1, c]

private noncomputable def simpleCorootTorusPoint (i : Fin 2) (c : kˣ) :
    Variety.Point (dVariety k 2) :=
  (dPointEquiv 2).symm (simpleCorootTorusParameter i c)

private noncomputable def simpleCorootTorusFactor (i : Fin 2) (c : kˣ) :
    CarrierPoint (k := k) :=
  (splitTorusMorphism (k := k)).onPoints (simpleCorootTorusPoint i c)

omit [IsAlgClosed k] in
private theorem simpleCorootTorusParameter_eq (i : Fin 2) (c : kˣ) :
    simpleCorootTorusParameter i c =
      rootCorootTorusParameter (simpleRoot i) c := by
  fin_cases i <;> rfl

private theorem simpleCorootTorusFactor_eq (i : Fin 2) (c : kˣ) :
    simpleCorootTorusFactor (k := k) i c =
      rootCorootTorusFactor (k := k) (simpleRoot i) c := by
  fin_cases i <;> rfl

/-- The simple root of the same length used to construct a representative for `r`. -/
@[expose] public def rootBaseIndex : Root → Fin 2
  | 0 | 2 | 3 | 6 | 8 | 9 => 0
  | _ => 1

/-- A simple-reflection word carrying `rootBaseIndex r` to `r` without a parameter sign. -/
@[expose] public def rootTransportWord : Root → List (Fin 2)
  | 0 | 1 => []
  | 2 => [1]
  | 3 => [1, 0]
  | 4 => [0]
  | 5 => [0, 1]
  | 6 => [0]
  | 7 => [1]
  | 8 => [0, 1]
  | 9 => [0, 1, 0]
  | 10 => [1, 0]
  | 11 => [1, 0, 1]

private def wordRootAction : List (Fin 2) → Root → Root
  | [], r => r
  | i :: w, r => wordRootAction w (simpleReflection i r)

private def wordRootParameter {R : Type*} [CommRing R] :
    List (Fin 2) → Root → R → R
  | [], _, a => a
  | i :: w, r, a =>
      wordRootParameter w (simpleReflection i r)
        ((weylRootSign i r : R) * a)

private theorem rootTransport_action (r : Root) :
    wordRootAction (rootTransportWord r) (simpleRoot (rootBaseIndex r)) = r := by
  fin_cases r <;> rfl

private theorem rootTransport_neg_action (r : Root) :
    wordRootAction (rootTransportWord r) (-simpleRoot (rootBaseIndex r)) = -r := by
  fin_cases r <;> rfl

omit [IsAlgClosed k] in
private theorem rootTransport_parameter (r : Root) (a : k) :
    wordRootParameter (R := k) (rootTransportWord r)
        (simpleRoot (rootBaseIndex r)) a = a := by
  fin_cases r <;> simp [rootTransportWord, rootBaseIndex, wordRootParameter,
    simpleRoot, Root.short, Root.long, simpleReflection, weylRootSign]

omit [IsAlgClosed k] in
private theorem rootTransport_neg_parameter (r : Root) (a : k) :
    wordRootParameter (R := k) (rootTransportWord r)
        (-simpleRoot (rootBaseIndex r)) a = a := by
  change wordRootParameter (R := k) (rootTransportWord r)
      (Root.neg (simpleRoot (rootBaseIndex r))) a = a
  fin_cases r <;> simp [rootTransportWord, rootBaseIndex, wordRootParameter,
    simpleRoot, Root.short, Root.long, simpleReflection, weylRootSign,
    Root.neg]

/-- Product of the certified simple Weyl representatives in a reflection word. -/
@[expose] public noncomputable def carrierWeylWord :
    List (Fin 2) → CarrierPoint (k := k)
  | [] => 1
  | i :: w =>
      carrierWeylRepresentative (k := k) i * carrierWeylWord w

/-- The same word written as a product of certified inverse simple representatives. -/
@[expose] public noncomputable def carrierWeylWordInv :
    List (Fin 2) → CarrierPoint (k := k)
  | [] => 1
  | i :: w =>
      carrierWeylWordInv w * carrierWeylRepresentativeInv (k := k) i

/-- The explicit inverse word is the group inverse of `carrierWeylWord`. -/
public theorem carrierWeylWordInv_eq_inv (w : List (Fin 2)) :
    carrierWeylWordInv (k := k) w = (carrierWeylWord (k := k) w)⁻¹ := by
  induction w with
  | nil => simp [carrierWeylWord, carrierWeylWordInv]
  | cons i w ih =>
      rw [carrierWeylWordInv, carrierWeylWord, ih,
        mul_inv_rev, carrierWeylRepresentative_inv]

private theorem carrierWeylWord_root_conjugation
    (w : List (Fin 2)) (r : Root) (a : k) :
    (carrierWeylWord (k := k) w)⁻¹ *
        (rootMorphism (k := k) r).onPoints (kPlusPoint a) *
        carrierWeylWord (k := k) w =
      (rootMorphism (k := k) (wordRootAction w r)).onPoints
        (kPlusPoint (wordRootParameter (R := k) w r a)) := by
  induction w generalizing r a with
  | nil => simp [carrierWeylWord, wordRootAction, wordRootParameter]
  | cons i w ih =>
      rw [carrierWeylWord, mul_inv_rev]
      calc
        _ = (carrierWeylWord (k := k) w)⁻¹ *
              ((carrierWeylRepresentative (k := k) i)⁻¹ *
                (rootMorphism (k := k) r).onPoints (kPlusPoint a) *
                carrierWeylRepresentative (k := k) i) *
              carrierWeylWord (k := k) w := by group
        _ = (carrierWeylWord (k := k) w)⁻¹ *
              (rootMorphism (k := k) (simpleReflection i r)).onPoints
                (kPlusPoint ((weylRootSign i r : k) * a)) *
              carrierWeylWord (k := k) w := by
                rw [carrierWeylRepresentative_rootMorphism_conjugation]
        _ = _ := ih (simpleReflection i r) ((weylRootSign i r : k) * a)

private theorem rootTransport_root_conjugation (r : Root) (a : k) :
    (carrierWeylWord (k := k) (rootTransportWord r))⁻¹ *
        (rootMorphism (k := k) (simpleRoot (rootBaseIndex r))).onPoints
          (kPlusPoint a) *
        carrierWeylWord (k := k) (rootTransportWord r) =
      (rootMorphism (k := k) r).onPoints (kPlusPoint a) := by
  rw [carrierWeylWord_root_conjugation, rootTransport_action,
    rootTransport_parameter]

private theorem rootTransport_neg_root_conjugation (r : Root) (a : k) :
    (carrierWeylWord (k := k) (rootTransportWord r))⁻¹ *
        (rootMorphism (k := k) (-simpleRoot (rootBaseIndex r))).onPoints
          (kPlusPoint a) *
        carrierWeylWord (k := k) (rootTransportWord r) =
      (rootMorphism (k := k) (-r)).onPoints (kPlusPoint a) := by
  rw [carrierWeylWord_root_conjugation, rootTransport_neg_action,
    rootTransport_neg_parameter]

private def wordTorusParameter {R : Type*} [CommRing R] :
    List (Fin 2) → TorusParameter R → TorusParameter R
  | [], u => u
  | i :: w, u =>
      wordTorusParameter w (simpleReflectionTorusParameter i u)

omit [IsAlgClosed k] in
private theorem rootTransport_torusParameter (r : Root) (c : kˣ) :
    wordTorusParameter (rootTransportWord r)
        (simpleCorootTorusParameter (rootBaseIndex r) c) =
      rootCorootTorusParameter r c := by
  fin_cases r <;>
    funext i <;> fin_cases i <;>
    simp [rootTransportWord, rootBaseIndex, wordTorusParameter,
      simpleCorootTorusParameter, simpleReflectionTorusParameter,
      rootCorootTorusParameter, mul_comm] <;> group

private theorem carrierSimpleWeyl_dTorus_conjugation
    (i : Fin 2) (x : Variety.Point (dVariety k 2)) :
    (carrierWeylRepresentative (k := k) i)⁻¹ *
        (splitTorusMorphism (k := k)).onPoints x *
        carrierWeylRepresentative (k := k) i =
      (splitTorusMorphism (k := k)).onPoints
        ((dPointEquiv 2).symm
          (simpleReflectionTorusParameter i (dPointEquiv 2 x))) := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  have h := carrierWeylRepresentative_splitTorus_conjugation (k := k) i
    ((splitTorusIso (k := k)).hom.onPoints x)
  simp only [simpleReflectionTorusPoint] at h
  rw [(splitTorusIso (k := k)).hom_inv_id] at h
  change (carrierWeylRepresentative (k := k) i)⁻¹ *
      (splitTorus (k := k)).inclusion.onPoints
        ((splitTorusIso (k := k)).hom.onPoints x) *
      carrierWeylRepresentative (k := k) i =
    (splitTorus (k := k)).inclusion.onPoints
      ((splitTorusIso (k := k)).hom.onPoints
        ((dPointEquiv 2).symm
          (simpleReflectionTorusParameter i (dPointEquiv 2 x)))) at h
  rw [splitTorusIso_inclusion_apply, splitTorusIso_inclusion_apply] at h
  exact h

private theorem carrierWeylWord_dTorus_conjugation
    (w : List (Fin 2)) (x : Variety.Point (dVariety k 2)) :
    (carrierWeylWord (k := k) w)⁻¹ *
        (splitTorusMorphism (k := k)).onPoints x *
        carrierWeylWord (k := k) w =
      (splitTorusMorphism (k := k)).onPoints
        ((dPointEquiv 2).symm
          (wordTorusParameter w (dPointEquiv 2 x))) := by
  induction w generalizing x with
  | nil =>
      simp [carrierWeylWord, wordTorusParameter]
  | cons i w ih =>
      rw [carrierWeylWord, mul_inv_rev]
      calc
        _ = (carrierWeylWord (k := k) w)⁻¹ *
              ((carrierWeylRepresentative (k := k) i)⁻¹ *
                (splitTorusMorphism (k := k)).onPoints x *
                carrierWeylRepresentative (k := k) i) *
              carrierWeylWord (k := k) w := by group
        _ = (carrierWeylWord (k := k) w)⁻¹ *
              (splitTorusMorphism (k := k)).onPoints
                ((dPointEquiv 2).symm
                  (simpleReflectionTorusParameter i (dPointEquiv 2 x))) *
              carrierWeylWord (k := k) w := by
                rw [carrierSimpleWeyl_dTorus_conjugation]
        _ = _ := by
          rw [ih]
          congr 2

private theorem rootTransport_torus_conjugation (r : Root) (c : kˣ) :
    (carrierWeylWord (k := k) (rootTransportWord r))⁻¹ *
        simpleCorootTorusFactor (k := k) (rootBaseIndex r) c *
        carrierWeylWord (k := k) (rootTransportWord r) =
      rootCorootTorusFactor (k := k) r c := by
  simp only [simpleCorootTorusFactor]
  rw [carrierWeylWord_dTorus_conjugation]
  congr 1
  apply (dPointEquiv 2).injective
  simp [simpleCorootTorusPoint, rootCorootTorusPoint,
    rootTransport_torusParameter]

/-- A Weyl representative for `r`, conjugated from the certified simple representative. -/
@[expose] public noncomputable def rootWeylRepresentative (r : Root) :
    CarrierPoint (k := k) :=
  carrierWeylWordInv (k := k) (rootTransportWord r) *
    carrierWeylRepresentative (k := k) (rootBaseIndex r) *
    carrierWeylWord (k := k) (rootTransportWord r)

/-- The corresponding representative built from the certified simple inverse. -/
@[expose] public noncomputable def rootWeylRepresentativeInv (r : Root) :
    CarrierPoint (k := k) :=
  carrierWeylWordInv (k := k) (rootTransportWord r) *
    carrierWeylRepresentativeInv (k := k) (rootBaseIndex r) *
    carrierWeylWord (k := k) (rootTransportWord r)

/-- The displayed inverse representative is the inverse of `rootWeylRepresentative`. -/
public theorem rootWeylRepresentative_inv (r : Root) :
    (rootWeylRepresentative (k := k) r)⁻¹ =
      rootWeylRepresentativeInv (k := k) r := by
  simp only [rootWeylRepresentative, rootWeylRepresentativeInv,
    mul_inv_rev, carrierWeylWordInv_eq_inv,
    carrierWeylRepresentative_inv, inv_inv]
  group

/-- Conversely, inverting the displayed inverse recovers the root representative. -/
public theorem rootWeylRepresentativeInv_inv (r : Root) :
    (rootWeylRepresentativeInv (k := k) r)⁻¹ =
      rootWeylRepresentative (k := k) r := by
  rw [← rootWeylRepresentative_inv, inv_inv]

private def lowerTorusMatrix {R : Type*} [CommRing R]
    (r : Root) (t : R) (u : TorusParameter R) : Matrix Basis Basis R :=
  fun i j => rootCurve r t i j * (basisTorusUnit u j : R)

private theorem rootCurve_mul_torusElement {R : Type*} [CommRing R]
    (r : Root) (t : R) (u : TorusParameter R) :
    rootCurve r t * (torusElement u : Matrix Basis Basis R) =
      lowerTorusMatrix r t u := by
  ext i j
  exact Matrix.mul_diagonal _ _ _ _

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem short_rootCurveUnit_nonsingular {R : Type*} [Field R]
    (a b : R) (c : Rˣ) (hc : (c : R) = 1 - a * b) :
    rootCurveUnit (R := R) 0 a * rootCurveUnit 6 b =
      rootCurveUnit 6 (b * (c⁻¹ : Rˣ)) *
        torusElement (simpleCorootTorusParameter 0 c⁻¹) *
        rootCurveUnit 0 (a * (c⁻¹ : Rˣ)) := by
  apply Units.ext
  change rootCurve 0 a * rootCurve 6 b =
    (rootCurve 6 (b * (c⁻¹ : Rˣ)) *
      (torusElement (simpleCorootTorusParameter 0 c⁻¹) :
        Matrix Basis Basis R)) *
      rootCurve 0 (a * (c⁻¹ : Rˣ))
  rw [rootCurve_mul_torusElement]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerTorusMatrix, rootCurve, rootDividedPower, rootOperator,
      rootOperatorEntries, rootDividedPowerTwoEntries,
      rootDividedPowerThreeEntries, specialize, matrixOfEntries,
      simpleCorootTorusParameter, basisTorusUnit, basisWeight, basisRoot,
      Root.pairingSimple, Root.coord, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ] <;>
    field_simp [Units.ne_zero c]
  all_goals try rw [hc]
  all_goals ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem long_rootCurveUnit_nonsingular {R : Type*} [Field R]
    (a b : R) (c : Rˣ) (hc : (c : R) = 1 - a * b) :
    rootCurveUnit (R := R) 1 a * rootCurveUnit 7 b =
      rootCurveUnit 7 (b * (c⁻¹ : Rˣ)) *
        torusElement (simpleCorootTorusParameter 1 c⁻¹) *
        rootCurveUnit 1 (a * (c⁻¹ : Rˣ)) := by
  apply Units.ext
  change rootCurve 1 a * rootCurve 7 b =
    (rootCurve 7 (b * (c⁻¹ : Rˣ)) *
      (torusElement (simpleCorootTorusParameter 1 c⁻¹) :
        Matrix Basis Basis R)) *
      rootCurve 1 (a * (c⁻¹ : Rˣ))
  rw [rootCurve_mul_torusElement]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerTorusMatrix, rootCurve, rootDividedPower, rootOperator,
      rootOperatorEntries, rootDividedPowerTwoEntries,
      rootDividedPowerThreeEntries, specialize, matrixOfEntries,
      simpleCorootTorusParameter, basisTorusUnit, basisWeight, basisRoot,
      Root.pairingSimple, Root.coord, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ] <;>
    field_simp [Units.ne_zero c]
  all_goals try rw [hc]
  all_goals ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem short_rootCurveUnit_singular {R : Type*} [Field R]
    (a b : R) (d : Rˣ) (hd : (d : R) = b) (hab : a * b = 1) :
    rootCurveUnit (R := R) 0 a * rootCurveUnit 6 b =
      rootCurveUnit 6 (-b) *
        torusElement (simpleCorootTorusParameter 0 d) *
        weylMatrixUnit 0 := by
  have hb : b ≠ 0 := right_ne_zero_of_mul_eq_one hab
  have ha : a = b⁻¹ := by
    apply mul_right_cancel₀ hb
    rw [hab, inv_mul_cancel₀ hb]
  have hd' : d = Units.mk0 b hb := by
    apply Units.ext
    exact hd
  apply Units.ext
  change rootCurve 0 a * rootCurve 6 b =
    (rootCurve 6 (-b) *
      (torusElement (simpleCorootTorusParameter 0 d) :
        Matrix Basis Basis R)) *
      specialize (weyl 0)
  rw [ha, hd', rootCurve_mul_torusElement]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerTorusMatrix, rootCurve, rootDividedPower, rootOperator,
      rootOperatorEntries, rootDividedPowerTwoEntries,
      rootDividedPowerThreeEntries, specialize, matrixOfEntries,
      simpleCorootTorusParameter, basisTorusUnit, basisWeight, basisRoot,
      Root.pairingSimple, Root.coord, weyl, weylEntries, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ]
  all_goals try field_simp [hb]
  all_goals ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem long_rootCurveUnit_singular {R : Type*} [Field R]
    (a b : R) (d : Rˣ) (hd : (d : R) = b) (hab : a * b = 1) :
    rootCurveUnit (R := R) 1 a * rootCurveUnit 7 b =
      rootCurveUnit 7 (-b) *
        torusElement (simpleCorootTorusParameter 1 d) *
        weylMatrixUnit 1 := by
  have hb : b ≠ 0 := right_ne_zero_of_mul_eq_one hab
  have ha : a = b⁻¹ := by
    apply mul_right_cancel₀ hb
    rw [hab, inv_mul_cancel₀ hb]
  have hd' : d = Units.mk0 b hb := by
    apply Units.ext
    exact hd
  apply Units.ext
  change rootCurve 1 a * rootCurve 7 b =
    (rootCurve 7 (-b) *
      (torusElement (simpleCorootTorusParameter 1 d) :
        Matrix Basis Basis R)) *
      specialize (weyl 1)
  rw [ha, hd', rootCurve_mul_torusElement]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerTorusMatrix, rootCurve, rootDividedPower, rootOperator,
      rootOperatorEntries, rootDividedPowerTwoEntries,
      rootDividedPowerThreeEntries, specialize, matrixOfEntries,
      simpleCorootTorusParameter, basisTorusUnit, basisWeight, basisRoot,
      Root.pairingSimple, Root.coord, weyl, weylEntries, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ]
  all_goals try field_simp [hb]
  all_goals ring

private theorem simple_rootCurveUnit_nonsingular
    {R : Type*} [Field R] (i : Fin 2) (a b : R) (c : Rˣ)
    (hc : (c : R) = 1 - a * b) :
    rootCurveUnit (simpleRoot i) a * rootCurveUnit (-simpleRoot i) b =
      rootCurveUnit (-simpleRoot i) (b * (c⁻¹ : Rˣ)) *
        torusElement (simpleCorootTorusParameter i c⁻¹) *
        rootCurveUnit (simpleRoot i) (a * (c⁻¹ : Rˣ)) := by
  fin_cases i
  · exact short_rootCurveUnit_nonsingular a b c hc
  · exact long_rootCurveUnit_nonsingular a b c hc

private theorem simple_rootCurveUnit_singular
    {R : Type*} [Field R] (i : Fin 2) (a b : R) (d : Rˣ)
    (hd : (d : R) = b) (hab : a * b = 1) :
    rootCurveUnit (simpleRoot i) a * rootCurveUnit (-simpleRoot i) b =
      rootCurveUnit (-simpleRoot i) (-b) *
        torusElement (simpleCorootTorusParameter i d) *
        weylMatrixUnit i := by
  fin_cases i
  · exact short_rootCurveUnit_singular a b d hd hab
  · exact long_rootCurveUnit_singular a b d hd hab

private noncomputable def ambientRepresentationPointHom :
    LinearMap.GeneralLinearGroup k (Basis → k) →*
      Variety.Point (Ambient k) where
  toFun g := generalLinearRepresentationPoint (carrierBasis (k := k)) g
  map_one' := by
    simpa [Ambient, glVarietyOf] using
      generalLinearRepresentationPoint_one (carrierBasis (k := k))
  map_mul' g h := by
    simpa [Ambient, glVarietyOf] using
      generalLinearRepresentationPoint_mul (carrierBasis (k := k)) g h

omit [IsAlgClosed k] in
private lemma kPlusPoint_value (a : k) :
    (kPlusPoint a).val PUnit.unit = a := rfl

private theorem simple_carrier_nonsingular
    (i : Fin 2) (a b : k) (c : kˣ) (hc : (c : k) = 1 - a * b) :
    (rootMorphism (k := k) (simpleRoot i)).onPoints (kPlusPoint a) *
        (rootMorphism (k := k) (-simpleRoot i)).onPoints (kPlusPoint b) =
      (rootMorphism (k := k) (-simpleRoot i)).onPoints
          (kPlusPoint (b * (c⁻¹ : kˣ))) *
        simpleCorootTorusFactor (k := k) i c⁻¹ *
        (rootMorphism (k := k) (simpleRoot i)).onPoints
          (kPlusPoint (a * (c⁻¹ : kˣ))) := by
  apply (ambientClosedCarrier (k := k)).inclusion_injective
  simp only [map_mul]
  simp only [simpleCorootTorusFactor]
  rw [rootMorphism_inclusion_apply, rootMorphism_inclusion_apply,
    rootMorphism_inclusion_apply, rootMorphism_inclusion_apply,
    splitTorusMorphism_inclusion_apply]
  simp only [rootAmbientMorphism_apply, torusAmbientMorphism_apply]
  let ρ := ambientRepresentationPointHom (k := k)
  change ρ _ * ρ _ = ρ _ * ρ _ * ρ _
  simp only [← ρ.map_mul]
  congr 1
  simpa [rootPointRepresentation, torusPointRepresentation,
      simpleCorootTorusPoint, kPlusPoint_value] using
    congrArg Matrix.GeneralLinearGroup.toLin
      (simple_rootCurveUnit_nonsingular i a b c hc)

private theorem simple_carrier_singular
    (i : Fin 2) (a b : k) (d : kˣ)
    (hd : (d : k) = b) (hab : a * b = 1) :
    (rootMorphism (k := k) (simpleRoot i)).onPoints (kPlusPoint a) *
        (rootMorphism (k := k) (-simpleRoot i)).onPoints (kPlusPoint b) =
      (rootMorphism (k := k) (-simpleRoot i)).onPoints (kPlusPoint (-b)) *
        simpleCorootTorusFactor (k := k) i d *
        carrierWeylRepresentative (k := k) i := by
  apply (ambientClosedCarrier (k := k)).inclusion_injective
  simp only [map_mul]
  simp only [simpleCorootTorusFactor]
  rw [rootMorphism_inclusion_apply, rootMorphism_inclusion_apply,
    rootMorphism_inclusion_apply, splitTorusMorphism_inclusion_apply,
    carrierWeylRepresentative_ambient_matrix]
  simp only [rootAmbientMorphism_apply, torusAmbientMorphism_apply]
  let ρ := ambientRepresentationPointHom (k := k)
  change ρ _ * ρ _ = ρ _ * ρ _ * ρ _
  simp only [← ρ.map_mul]
  congr 1
  simpa [rootPointRepresentation, torusPointRepresentation,
      simpleCorootTorusPoint, kPlusPoint_value] using
    congrArg Matrix.GeneralLinearGroup.toLin
      (simple_rootCurveUnit_singular i a b d hd hab)

/-- Pointwise opposite-root Gauss factorization when `1 - a * b` is nonzero. -/
public theorem carrier_oppositeRootProduct_nonsingular
    (r : Root) (a b : k) (hc : 1 - a * b ≠ 0) :
    let c : kˣ := Units.mk0 (1 - a * b) hc
    (rootMorphism (k := k) r).onPoints (kPlusPoint a) *
        (rootMorphism (k := k) (-r)).onPoints (kPlusPoint b) =
      (rootMorphism (k := k) (-r)).onPoints
          (kPlusPoint (b * (c⁻¹ : kˣ))) *
        rootCorootTorusFactor (k := k) r c⁻¹ *
        (rootMorphism (k := k) r).onPoints
          (kPlusPoint (a * (c⁻¹ : kˣ))) := by
  dsimp only
  let w := rootTransportWord r
  let i := rootBaseIndex r
  let g := carrierWeylWord (k := k) w
  let c : kˣ := Units.mk0 (1 - a * b) hc
  have hs := simple_carrier_nonsingular (k := k) i a b c rfl
  have hpos (t : k) :
      g⁻¹ * (rootMorphism (k := k) (simpleRoot i)).onPoints (kPlusPoint t) * g =
        (rootMorphism (k := k) r).onPoints (kPlusPoint t) := by
    simpa [g, w, i] using rootTransport_root_conjugation (k := k) r t
  have hneg (t : k) :
      g⁻¹ * (rootMorphism (k := k) (-simpleRoot i)).onPoints (kPlusPoint t) * g =
        (rootMorphism (k := k) (-r)).onPoints (kPlusPoint t) := by
    simpa [g, w, i] using rootTransport_neg_root_conjugation (k := k) r t
  have htor :
      g⁻¹ * simpleCorootTorusFactor (k := k) i c⁻¹ * g =
        rootCorootTorusFactor (k := k) r c⁻¹ := by
    simpa [g, w, i] using rootTransport_torus_conjugation (k := k) r c⁻¹
  rw [← hpos a, ← hneg b]
  calc
    (g⁻¹ * _ * g) * (g⁻¹ * _ * g) =
        g⁻¹ *
          ((rootMorphism (k := k) (simpleRoot i)).onPoints (kPlusPoint a) *
            (rootMorphism (k := k) (-simpleRoot i)).onPoints (kPlusPoint b)) *
          g := by group
    _ = g⁻¹ *
          ((rootMorphism (k := k) (-simpleRoot i)).onPoints
              (kPlusPoint (b * (c⁻¹ : kˣ))) *
            simpleCorootTorusFactor (k := k) i c⁻¹ *
            (rootMorphism (k := k) (simpleRoot i)).onPoints
              (kPlusPoint (a * (c⁻¹ : kˣ)))) *
          g := by rw [hs]
    _ = (g⁻¹ *
            (rootMorphism (k := k) (-simpleRoot i)).onPoints
              (kPlusPoint (b * (c⁻¹ : kˣ))) * g) *
          (g⁻¹ * simpleCorootTorusFactor (k := k) i c⁻¹ * g) *
          (g⁻¹ *
            (rootMorphism (k := k) (simpleRoot i)).onPoints
              (kPlusPoint (a * (c⁻¹ : kˣ))) * g) := by group
    _ = _ := by rw [hneg, htor, hpos]

/-- Pointwise singular exchange when `a * b = 1`, ending in the root Weyl lift. -/
public theorem carrier_oppositeRootProduct_singular
    (r : Root) (a b : k) (hab : a * b = 1) :
    let d : kˣ := Units.mk0 b (right_ne_zero_of_mul_eq_one hab)
    (rootMorphism (k := k) r).onPoints (kPlusPoint a) *
        (rootMorphism (k := k) (-r)).onPoints (kPlusPoint b) =
      (rootMorphism (k := k) (-r)).onPoints (kPlusPoint (-b)) *
        rootCorootTorusFactor (k := k) r d *
        rootWeylRepresentative (k := k) r := by
  dsimp only
  let w := rootTransportWord r
  let i := rootBaseIndex r
  let g := carrierWeylWord (k := k) w
  let d : kˣ := Units.mk0 b (right_ne_zero_of_mul_eq_one hab)
  have hs := simple_carrier_singular (k := k) i a b d rfl hab
  have hpos (t : k) :
      g⁻¹ * (rootMorphism (k := k) (simpleRoot i)).onPoints (kPlusPoint t) * g =
        (rootMorphism (k := k) r).onPoints (kPlusPoint t) := by
    simpa [g, w, i] using rootTransport_root_conjugation (k := k) r t
  have hneg (t : k) :
      g⁻¹ * (rootMorphism (k := k) (-simpleRoot i)).onPoints (kPlusPoint t) * g =
        (rootMorphism (k := k) (-r)).onPoints (kPlusPoint t) := by
    simpa [g, w, i] using rootTransport_neg_root_conjugation (k := k) r t
  have htor :
      g⁻¹ * simpleCorootTorusFactor (k := k) i d * g =
        rootCorootTorusFactor (k := k) r d := by
    simpa [g, w, i] using rootTransport_torus_conjugation (k := k) r d
  have hn :
      g⁻¹ * carrierWeylRepresentative (k := k) i * g =
        rootWeylRepresentative (k := k) r := by
    simp [rootWeylRepresentative, g, w, i, carrierWeylWordInv_eq_inv]
  rw [← hpos a, ← hneg b]
  calc
    (g⁻¹ * _ * g) * (g⁻¹ * _ * g) =
        g⁻¹ *
          ((rootMorphism (k := k) (simpleRoot i)).onPoints (kPlusPoint a) *
            (rootMorphism (k := k) (-simpleRoot i)).onPoints (kPlusPoint b)) *
          g := by group
    _ = g⁻¹ *
          ((rootMorphism (k := k) (-simpleRoot i)).onPoints (kPlusPoint (-b)) *
            simpleCorootTorusFactor (k := k) i d *
            carrierWeylRepresentative (k := k) i) *
          g := by rw [hs]
    _ = (g⁻¹ *
            (rootMorphism (k := k) (-simpleRoot i)).onPoints
              (kPlusPoint (-b)) * g) *
          (g⁻¹ * simpleCorootTorusFactor (k := k) i d * g) *
          (g⁻¹ * carrierWeylRepresentative (k := k) i * g) := by group
    _ = _ := by rw [hneg, htor, hn]

/-- Every opposite-root product lies in exactly the singular or nonsingular exchange branch. -/
public theorem carrier_oppositeRootProduct_exchange
    (r : Root) (a b : k) :
    (1 - a * b = 0 ∧
      ∃ d : kˣ,
        (d : k) = b ∧
        (rootMorphism (k := k) r).onPoints (kPlusPoint a) *
            (rootMorphism (k := k) (-r)).onPoints (kPlusPoint b) =
          (rootMorphism (k := k) (-r)).onPoints (kPlusPoint (-b)) *
            rootCorootTorusFactor (k := k) r d *
            rootWeylRepresentative (k := k) r) ∨
    (1 - a * b ≠ 0 ∧
      ∃ c : kˣ,
        (c : k) = 1 - a * b ∧
        (rootMorphism (k := k) r).onPoints (kPlusPoint a) *
            (rootMorphism (k := k) (-r)).onPoints (kPlusPoint b) =
          (rootMorphism (k := k) (-r)).onPoints
              (kPlusPoint (b * (c⁻¹ : kˣ))) *
            rootCorootTorusFactor (k := k) r c⁻¹ *
            (rootMorphism (k := k) r).onPoints
              (kPlusPoint (a * (c⁻¹ : kˣ)))) := by
  by_cases hc : 1 - a * b = 0
  · left
    have hab : a * b = 1 := by linear_combination -hc
    let d : kˣ := Units.mk0 b (right_ne_zero_of_mul_eq_one hab)
    refine ⟨hc, d, rfl, ?_⟩
    exact carrier_oppositeRootProduct_singular r a b hab
  · right
    let c : kˣ := Units.mk0 (1 - a * b) hc
    refine ⟨hc, c, rfl, ?_⟩
    exact carrier_oppositeRootProduct_nonsingular r a b hc

end Theory.AlgebraicGroup.G2Chevalley
