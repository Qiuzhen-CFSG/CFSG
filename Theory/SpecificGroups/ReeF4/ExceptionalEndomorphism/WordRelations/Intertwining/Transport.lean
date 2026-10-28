module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.Curves
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Lift
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.RootDuality.Negation

/-!
# Transport for the exceptional F4 comparison

Exceptional duality intertwines simple reflections and their Weyl words. The
`Curves` extension identifies each actual canonical root curve with its signed
simple curve transported by an integral Tits word, and compares the reversed
route with the independently chosen route to the dual root in characteristic
two. It also verifies the parameter exponent along each route.

The concrete singular quotient-to-ideal map respects products, inverses and
conjugation whenever the corresponding matrices intertwine. Applying these
facts to the simple-root factors of each Tits generator proves that both signs
of simple-root intertwining suffice for all canonical F4 root curves. The
simple-root identities remain explicit inputs to this reduction; this module
does not assert that the exceptional endomorphism has already been constructed.

The coordinate convention and source are those of `RootDuality` and
`Coordinates`, following Aschbacher–Smith, Remark A.2.4, with integral root
curves as in Steinberg, *Lectures on Chevalley Groups*.
-/

public section

namespace ReeF4.WordRelations

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Classical Matrix

noncomputable local instance : Fintype
    Theory.AlgebraicGroup.StandardRootSystem.typeF4Roots := Fintype.ofFinite _

/-- Conjugation transports an intertwining identity for the concrete singular
comparison matrix. Its invertibility is neither needed nor asserted. -/
theorem quotientToIdeal_intertwines_conjugate {S : Type*} [CommRing S]
    (u v x y : (Matrix Coordinate Coordinate S)ˣ)
    (hu : quotientToIdeal * (u : Matrix Coordinate Coordinate S) =
      (v : Matrix Coordinate Coordinate S) * quotientToIdeal)
    (hx : quotientToIdeal * (x : Matrix Coordinate Coordinate S) =
      (y : Matrix Coordinate Coordinate S) * quotientToIdeal) :
    quotientToIdeal * (↑(u * x * u⁻¹) : Matrix Coordinate Coordinate S) =
      (↑(v * y * v⁻¹) : Matrix Coordinate Coordinate S) * quotientToIdeal := by
  have hi := intertwines_inv quotientToIdeal u v hu
  simp only [Units.val_mul]
  calc
    quotientToIdeal * (u.val * x.val * (u⁻¹).val) =
        (quotientToIdeal * u.val) * x.val * (u⁻¹).val := by simp only [mul_assoc]
    _ = (v.val * quotientToIdeal) * x.val * (u⁻¹).val := by rw [hu]
    _ = v.val * (quotientToIdeal * x.val) * (u⁻¹).val := by simp only [mul_assoc]
    _ = v.val * (y.val * quotientToIdeal) * (u⁻¹).val := by rw [hx]
    _ = (v.val * y.val) * (quotientToIdeal * (u⁻¹).val) := by simp only [mul_assoc]
    _ = (v.val * y.val * (v⁻¹).val) * quotientToIdeal := by
      rw [hi]
      simp only [mul_assoc]

private theorem quotientToIdeal_intertwines_mul {S : Type*} [CommRing S]
    {u v x y : (Matrix Coordinate Coordinate S)ˣ}
    (hu : quotientToIdeal * u.val = v.val * quotientToIdeal)
    (hx : quotientToIdeal * x.val = y.val * quotientToIdeal) :
    quotientToIdeal * (u * x).val = (v * y).val * quotientToIdeal := by
  simp only [Units.val_mul]
  rw [← mul_assoc, hu, mul_assoc, hx, ← mul_assoc]

/-- Intertwining the signed simple curves at the Tits parameters intertwines
every integral Tits word with the word whose simple generators are reversed. -/
theorem quotientToIdeal_intertwines_titsUnit {S : Type*} [CommRing S]
    (hpositive : ∀ i : typeF4RootPairing_base.support,
      quotientToIdeal * (F4Chevalley.rootCurve i.val (1 : S)).val =
        (F4Chevalley.rootCurve (simplePermutation i).val 1).val * quotientToIdeal)
    (hnegative : ∀ i : typeF4RootPairing_base.support,
      letI := typeF4RootPairing.indexNeg
      quotientToIdeal * (F4Chevalley.rootCurve (-i.val) (-1 : S)).val =
        (F4Chevalley.rootCurve (-(simplePermutation i).val) (-1)).val * quotientToIdeal)
    (word : List typeF4RootPairing_base.support) :
    quotientToIdeal * (titsUnit (S := S) word).val =
      (titsUnit (word.map simplePermutation)).val * quotientToIdeal := by
  let := typeF4RootPairing.indexNeg
  induction word with
  | nil => simp only [List.map_nil, titsUnit_nil, Units.val_one, mul_one, one_mul]
  | cons i word ih =>
    rw [List.map_cons, titsUnit_cons, titsUnit_cons]
    exact quotientToIdeal_intertwines_mul
      (quotientToIdeal_intertwines_mul
        (quotientToIdeal_intertwines_mul (hpositive i) (hnegative i)) (hpositive i)) ih

/-- Both signs of simple-root intertwining imply the exact exceptional
intertwining identity for every canonical F4 curve. The only assumptions are
these simple-root identities; route comparison, Tits transport, and the
parameter exponent along the route are discharged here. -/
theorem quotientToIdeal_intertwines_all_roots_of_simple
    {S : Type*} [CommRing S] [CharP S 2]
    (hpositive : ∀ (i : typeF4RootPairing_base.support) (t : S),
      quotientToIdeal * (F4Chevalley.rootCurve i.val t).val =
        (F4Chevalley.rootCurve (exceptionalRootPermutation i.val)
          (exceptionalParameter i.val t)).val * quotientToIdeal)
    (hnegative : ∀ (i : typeF4RootPairing_base.support) (t : S),
      letI := typeF4RootPairing.indexNeg
      quotientToIdeal * (F4Chevalley.rootCurve (-i.val) t).val =
        (F4Chevalley.rootCurve (exceptionalRootPermutation (-i.val))
          (exceptionalParameter (-i.val) t)).val * quotientToIdeal)
    (r : typeF4Roots) (t : S) :
    quotientToIdeal * (F4Chevalley.rootCurve r t).val =
      (F4Chevalley.rootCurve (exceptionalRootPermutation r)
        (exceptionalParameter r t)).val * quotientToIdeal := by
  let := typeF4RootPairing.indexNeg
  have hparameter_one (s : typeF4Roots) : exceptionalParameter s (1 : S) = 1 := by
    by_cases hs : IsLongRoot s
    · rw [exceptionalParameter_of_long hs]
    · rw [exceptionalParameter_of_short hs, one_pow]
  have hword (word : List typeF4RootPairing_base.support) :
      quotientToIdeal * (titsUnit (S := S) word).val =
        (titsUnit (word.map simplePermutation)).val * quotientToIdeal := by
    apply quotientToIdeal_intertwines_titsUnit
    · intro i
      simpa only [simplePermutation_val, hparameter_one] using hpositive i 1
    · intro i
      simpa only [exceptionalRootPermutation_neg, simplePermutation_val,
        CharTwo.neg_eq, hparameter_one] using hnegative i (-1)
  have hpos (s : typeF4Roots) (hs : typeF4RootPairing_base.IsPos s) :
      quotientToIdeal * (F4Chevalley.rootCurve s t).val =
        (F4Chevalley.rootCurve (exceptionalRootPermutation s)
          (exceptionalParameter s t)).val * quotientToIdeal := by
    rw [rootCurve_of_pos_route s hs, rootCurve_dual_of_pos_route s hs]
    apply quotientToIdeal_intertwines_conjugate _ _ _ _ (hword _)
    simpa only [simplePermutation_val, exceptionalParameter_rootRoute] using
      hpositive (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) s).simple t
  have hneg (s : typeF4Roots) (hs : typeF4RootPairing_base.IsPos s) :
      quotientToIdeal * (F4Chevalley.rootCurve (-s) t).val =
        (F4Chevalley.rootCurve (exceptionalRootPermutation (-s))
          (exceptionalParameter (-s) t)).val * quotientToIdeal := by
    rw [rootCurve_neg_of_pos_route s hs, rootCurve_dual_neg_of_pos_route s hs]
    apply quotientToIdeal_intertwines_conjugate _ _ _ _ (hword _)
    simpa only [exceptionalRootPermutation_neg, simplePermutation_val,
      exceptionalParameter_neg, exceptionalParameter_rootRoute] using
      hnegative (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) s).simple t
  by_cases hr : typeF4RootPairing_base.IsPos r
  · exact hpos r hr
  · simpa only [neg_neg] using
      hneg (-r) ((RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base r).mpr hr)

end ReeF4.WordRelations
