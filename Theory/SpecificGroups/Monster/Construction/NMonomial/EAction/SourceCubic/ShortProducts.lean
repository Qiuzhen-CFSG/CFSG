module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.EAction.SourceCubic.MatrixBlocks
public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortFamilies.Odd
public import Theory.AtlasPort.OtherSporadic.Codes.GolayMinimum
/-!
# The all-short cubic table on the literal E pairs

The cocode images multiply without a central sign. The omega image is an
involution commuting with every pair image, as follows from the involution
laws for the actual `ru` and `rv` lifts. Hence a triple with an odd number
of `ru` factors has nonzero code coordinate and zero cubic coefficient;
an even triple reduces to the cocode image of the sum of its three pair words.

A cocode image never equals the distinguished central involution. Its identity
coefficient is detected by Golay membership. The sum of three pair words has
weight at most six, so the Golay minimum distance forces this sum to be zero.
For three pairs with distinct endpoints, that is precisely the triangle test.
Trilinearity on the unchanged vectors `v + u` and `v - u` now gives coefficient
four on equal-axis triangles and zero on every other triple. The final theorem
applies this calculation to the literal inclusions in the fixed Griess carrier.

Source: Aschbacher, *Sporadic Groups*, 27.8(4–5), (28.4), 28.8 and 29.11,
printed pp. 150–152 and 159–160. The Golay minimum theorem is reused from the
attributed ATLAS port; no external source code is copied here.
-/

@[expose] public section
open Sporadic.Monster.Construction
open LocalC ShortFamilies Griess TrialitySpin Atlas.Codes Atlas.Fischer
open scoped BigOperators
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.EAction.SourceCubic
attribute [local instance] Classical.propDecidable

private theorem cocode_add (J K : BinaryWord) : cocodeImage (J + K) = cocodeImage J * cocodeImage K := by
  simp only [cocodeImage, ← map_mul, q1Param_mul]
  simp [loopOne, q1WordProductSign, parkerSign, Submodule.Quotient.mk_add]

private theorem cocode_zero : cocodeImage 0 = 1 := by
  have h : q1Param (loopOne,0,0) = 1 := Subtype.ext q1Word_zero
  change q1ImageMap (q1Param (loopOne,0,Submodule.Quotient.mk (0 : BinaryWord))) = 1
  rw [show (Submodule.Quotient.mk (0 : BinaryWord) : Cocode) = 0 from rfl, h, map_one]

private theorem cocode_coordinates (J : BinaryWord) :
    (q1ImageCoordinates (cocodeImage J)).toAdd.cocode = Submodule.Quotient.mk J := by
  simp [cocodeImage, q1Coordinates_param, q1WordCoordinates]

private theorem omega_cocode_coordinates (J : BinaryWord) :
    (q1ImageCoordinates (loopImage parkerOmega * cocodeImage J)).toAdd.code = golayOne := by
  simp [map_mul, loopImage, cocodeImage, q1Coordinates_param, q1WordCoordinates,
    parkerOmega, loopOne, quadraticCoordinates_add_eq, coordinateSum]

private theorem center_coordinates : q1ImageCoordinates q1ImageCenterGenerator = 1 := by
  exact (show q1ImageCenterGenerator ∈ q1ImageCoordinates.ker from
    q1ImageCoordinates_kernel.symm ▸ centerGenerator_mem)

private theorem point_weight (x : Omega) : hammingNorm (pointWord x) = 1 := by
  simp [hammingNorm, pointWord, Pi.single_apply]
  have h : (Finset.univ.filter (fun i : Omega => i = x)) = {x} := by ext; simp
  rw [h]
  rfl

private theorem omega_pair_commute (x y : Omega) (hxy : x ≠ y) :
    Commute (loopImage parkerOmega) (cocodeImage (pairWord x y)) := by
  have hu := shortLift_square sourceLatticeComparison (ru x y hxy)
  have hv := shortLift_square sourceLatticeComparison (rv x y hxy)
  change (loopImage parkerOmega * cocodeImage (pairWord x y)) ^ 2 = 1 at hu
  change cocodeImage (pairWord x y) ^ 2 = 1 at hv
  rw [pow_two] at hu hv
  have iu := inv_eq_of_mul_eq_one_right hu
  have iv := inv_eq_of_mul_eq_one_right hv
  have hw : loopImage parkerOmega * loopImage parkerOmega = 1 := by
    rw [← pow_two, loopImage_omega_sq]
  have iw := inv_eq_of_mul_eq_one_right hw
  rw [mul_inv_rev, iv, iw] at iu
  exact iu.symm

private theorem cocode_eq_one (J : BinaryWord) : cocodeImage J = 1 ↔ J ∈ golay := by
  constructor
  · intro h
    have hc := congrArg (fun g : Q1Image => (q1ImageCoordinates g).toAdd.cocode) h
    rw [cocode_coordinates, map_one] at hc
    exact (Submodule.Quotient.mk_eq_zero golay).mp hc
  · intro h
    unfold cocodeImage
    rw [(Submodule.Quotient.mk_eq_zero golay).mpr h]
    exact cocode_zero

private theorem cocode_ne_center (J : BinaryWord) : cocodeImage J ≠ q1ImageCenterGenerator := by
  intro h
  have hc := congrArg (fun g : Q1Image => (q1ImageCoordinates g).toAdd.cocode) h
  rw [cocode_coordinates, center_coordinates] at hc
  have h1 := (cocode_eq_one J).mpr ((Submodule.Quotient.mk_eq_zero golay).mp hc)
  exact q1ImageCenterGenerator_ne_one (h.symm.trans h1)

private theorem central_cocode (J : BinaryWord) :
    centralCoefficient (cocodeImage J) = if J ∈ golay then 1 else 0 := by
  simp only [centralCoefficient, cocode_ne_center, if_false, sub_zero, cocode_eq_one]

private theorem central_omega_cocode (J : BinaryWord) :
    centralCoefficient (loopImage parkerOmega * cocodeImage J) = 0 := by
  have hn : golayOne ≠ 0 := by
    intro h
    have he := congrArg (fun a : golay => a.val (0,0)) h
    exact one_ne_zero he
  have h1 : loopImage parkerOmega * cocodeImage J ≠ 1 := by
    intro h
    have hc := congrArg (fun g : Q1Image => (q1ImageCoordinates g).toAdd.code) h
    rw [omega_cocode_coordinates, map_one] at hc
    exact hn hc
  have hz : loopImage parkerOmega * cocodeImage J ≠ q1ImageCenterGenerator := by
    intro h
    have hc := congrArg (fun g : Q1Image => (q1ImageCoordinates g).toAdd.code) h
    rw [omega_cocode_coordinates, center_coordinates] at hc
    exact hn hc
  simp [centralCoefficient, h1, hz]

private theorem pair_weight (x y : Omega) : hammingNorm (pairWord x y) ≤ 2 := by
  have h := binary_weight_add (pointWord x) (pointWord y)
  rw [point_weight, point_weight] at h
  change hammingNorm (pairWord x y) + _ = _ at h
  omega

private theorem triple_pair_mem (x y u v p q : Omega) :
    pairWord x y + pairWord u v + pairWord p q ∈ golay ↔
      pairWord x y + pairWord u v + pairWord p q = 0 := by
  constructor
  · intro h
    by_contra hn
    have hm := golay_minimum _ h hn
    have h₁ := binary_weight_add (pairWord x y) (pairWord u v)
    have h₂ := binary_weight_add (pairWord x y + pairWord u v) (pairWord p q)
    have hx := pair_weight x y
    have hu := pair_weight u v
    have hp := pair_weight p q
    omega
  · intro h
    rw [h]
    exact golay.zero_mem

private theorem ru_ru_product (x y u v : Omega) (hxy : x ≠ y) :
    ruElement x y * ruElement u v = cocodeImage (pairWord x y + pairWord u v) := by
  simp only [ruElement]
  rw [mul_assoc, ← mul_assoc (cocodeImage (pairWord x y)),
    ← (omega_pair_commute x y hxy).eq, mul_assoc,
    ← mul_assoc (loopImage parkerOmega), ← pow_two, loopImage_omega_sq, one_mul,
    ← cocode_add]

private theorem word_add_self (w : BinaryWord) : w + w = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (w i)

private theorem pairWord_ne_zero (x y : Omega) (hxy : x ≠ y) : pairWord x y ≠ 0 := by
  intro h
  have he := congrFun h x
  simp [pairWord, pointWord, hxy] at he

private theorem pairWord_eq_iff (x y p q : Omega) (hxy : x ≠ y) (hpq : p ≠ q) :
    pairWord x y = pairWord p q ↔ ({x,y} : Finset Omega) = {p,q} := by
  constructor
  · intro h
    rw [pairWord_support x y hxy, pairWord_support p q hpq] at h
    ext a
    have ha := congrFun h a
    by_cases h₁ : a ∈ ({x,y} : Finset Omega) <;>
      by_cases h₂ : a ∈ ({p,q} : Finset Omega) <;>
      simp_all [Atlas.Lattices.supportWord]
  · intro h
    rw [pairWord_support x y hxy, pairWord_support p q hpq, h]

private theorem two_pairs_zero (x y p q : Omega) (hxy : x ≠ y) (hpq : p ≠ q) :
    pairWord x y + pairWord p q = 0 ↔ ({x,y} : Finset Omega) = {p,q} := by
  rw [← pairWord_eq_iff x y p q hxy hpq]
  constructor
  · intro h
    have ht := congrArg (· + pairWord p q) h
    simpa [add_assoc, word_add_self] using ht
  · intro h
    rw [h, word_add_self]

private theorem pairWord_join (x y z : Omega) :
    pairWord x y + pairWord y z = pairWord x z := by
  simp only [pairWord]
  rw [add_assoc, ← add_assoc (pointWord y), word_add_self, zero_add]

private theorem pairWord_comm (x y : Omega) : pairWord x y = pairWord y x := add_comm _ _

private theorem disjoint_sum_ne_zero (x y u v p q : Omega)
    (hxy : x ≠ y) (huv : u ≠ v) (hxu : x ≠ u) (hxv : x ≠ v)
    (hyu : y ≠ u) (hyv : y ≠ v) :
    pairWord x y + pairWord u v + pairWord p q ≠ 0 := by
  intro h
  have hx : x = p ∨ x = q := by
    by_contra hn
    push Not at hn
    have he := congrFun h x
    simp [pairWord, pointWord, hxy, hxu, hxv, hn.1, hn.2] at he
  have hy : y = p ∨ y = q := by
    by_contra hn
    push Not at hn
    have he := congrFun h y
    simp [pairWord, pointWord, hxy.symm, hyu, hyv, hn.1, hn.2] at he
  have hu : u = p ∨ u = q := by
    by_contra hn
    push Not at hn
    have he := congrFun h u
    simp [pairWord, pointWord, hxu.symm, hyu.symm, huv, hn.1, hn.2] at he
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hu with hu | hu <;> grind

private theorem triangle_word (x y u v p q : Omega) (hxy : x ≠ y) (huv : u ≠ v) (hpq : p ≠ q) :
    triangle x y u v p q = if pairWord x y + pairWord u v + pairWord p q = 0 then 1 else 0 := by
  by_cases hxu : x = u
  · subst u
    by_cases hyv : y = v
    · subst v
      rw [triangle_repeat x y p q hxy hpq, word_add_self, zero_add,
        if_neg (pairWord_ne_zero p q hpq)]
    · rw [pairWord_comm x y, pairWord_join, triangle_expansion]
      simp only [two_pairs_zero y v p q hyv hpq]
      simp [hxy.symm, huv, hyv, edge_pair v y p q hpq,
        Finset.pair_comm v y]
  · by_cases hxv : x = v
    · subst v
      by_cases hyu : y = u
      · subst u
        rw [pairWord_comm y x, word_add_self, zero_add,
          if_neg (pairWord_ne_zero p q hpq), triangle_expansion]
        simp [hxy, hxy.symm, edge_diagonal p q hpq]
      · rw [pairWord_comm u x, pairWord_comm x y, pairWord_join, triangle_expansion]
        simp only [two_pairs_zero y u p q hyu hpq]
        simp [hxy.symm, hxu, hyu, edge_pair u y p q hpq,
          Finset.pair_comm u y]
    · by_cases hyu : y = u
      · subst u
        rw [pairWord_join, triangle_expansion]
        simp only [two_pairs_zero x v p q hxv hpq]
        simp [hxy, huv, hxv, edge_pair v x p q hpq,
          Finset.pair_comm v x]
      · by_cases hyv : y = v
        · subst v
          rw [pairWord_comm u y, pairWord_join, triangle_expansion]
          simp only [two_pairs_zero x u p q hxu hpq]
          simp [hxy, hyu, hxu, edge_pair u x p q hpq,
            Finset.pair_comm u x]
        · rw [triangle_disjoint x y u v p q hxu hxv hyu hyv,
            if_neg (disjoint_sum_ne_zero x y u v p q hxy huv hxu hxv hyu hyv)]

private theorem triangle_swap_first (x y u v p q : Omega)
    (hxy : x ≠ y) (huv : u ≠ v) (hpq : p ≠ q) :
    triangle x y u v p q = triangle u v x y p q := by
  rw [triangle_word x y u v p q hxy huv hpq, triangle_word u v x y p q huv hxy hpq,
    add_comm (pairWord x y) (pairWord u v)]

private theorem triangle_swap_last (x y u v p q : Omega)
    (hxy : x ≠ y) (huv : u ≠ v) (hpq : p ≠ q) :
    triangle x y u v p q = triangle x y p q u v := by
  rw [triangle_word x y u v p q hxy huv hpq, triangle_word x y p q u v hxy hpq huv,
    add_right_comm (pairWord x y) (pairWord u v) (pairWord p q)]

private theorem cubic_vvv (x y a b p q : Omega)
    (hxy : x ≠ y) (hab : a ≠ b) (hpq : p ≠ q) :
    shortCubic sourceLatticeComparison (v x y hxy) (v a b hab) (v p q hpq) =
      triangle x y a b p q := by
  rw [v, v, v, shortCubic_vector]
  change centralCoefficient (cocodeImage (pairWord x y) * cocodeImage (pairWord a b) *
    cocodeImage (pairWord p q)) = _
  rw [← cocode_add, ← cocode_add, central_cocode]
  simp only [triple_pair_mem]
  exact (triangle_word x y a b p q hxy hab hpq).symm

private theorem cubic_uvv (x y a b p q : Omega)
    (hxy : x ≠ y) (hab : a ≠ b) (hpq : p ≠ q) :
    shortCubic sourceLatticeComparison (u x y hxy) (v a b hab) (v p q hpq) = 0 := by
  rw [u, v, v, shortCubic_vector]
  change centralCoefficient ((loopImage parkerOmega * cocodeImage (pairWord x y)) *
    cocodeImage (pairWord a b) * cocodeImage (pairWord p q)) = _
  rw [mul_assoc (loopImage parkerOmega), ← cocode_add,
    mul_assoc (loopImage parkerOmega), ← cocode_add, central_omega_cocode]

private theorem cubic_uuv (x y a b p q : Omega)
    (hxy : x ≠ y) (hab : a ≠ b) (hpq : p ≠ q) :
    shortCubic sourceLatticeComparison (u x y hxy) (u a b hab) (v p q hpq) =
      triangle x y a b p q := by
  rw [u, u, v, shortCubic_vector]
  change centralCoefficient (ruElement x y * ruElement a b * cocodeImage (pairWord p q)) = _
  rw [ru_ru_product x y a b hxy, ← cocode_add, central_cocode]
  simp only [triple_pair_mem]
  exact (triangle_word x y a b p q hxy hab hpq).symm

private theorem cubic_uuu (x y a b p q : Omega)
    (hxy : x ≠ y) (hab : a ≠ b) (hpq : p ≠ q) :
    shortCubic sourceLatticeComparison (u x y hxy) (u a b hab) (u p q hpq) = 0 := by
  have hc := (omega_pair_commute x y hxy).mul_right (omega_pair_commute a b hab)
  rw [← cocode_add] at hc
  rw [u, u, u, shortCubic_vector]
  change centralCoefficient (ruElement x y * ruElement a b * ruElement p q) = _
  rw [ru_ru_product x y a b hxy, ruElement, ← mul_assoc, ← hc.eq,
    mul_assoc, ← cocode_add, central_omega_cocode]

private theorem cubic_vuv (x y a b p q : Omega)
    (hxy : x ≠ y) (hab : a ≠ b) (hpq : p ≠ q) :
    shortCubic sourceLatticeComparison (v x y hxy) (u a b hab) (v p q hpq) = 0 := by
  rw [shortCubic_swap_left, cubic_uvv]

private theorem cubic_vvu (x y a b p q : Omega)
    (hxy : x ≠ y) (hab : a ≠ b) (hpq : p ≠ q) :
    shortCubic sourceLatticeComparison (v x y hxy) (v a b hab) (u p q hpq) = 0 := by
  rw [shortCubic_swap_right, cubic_vuv]

private theorem cubic_uvu (x y a b p q : Omega)
    (hxy : x ≠ y) (hab : a ≠ b) (hpq : p ≠ q) :
    shortCubic sourceLatticeComparison (u x y hxy) (v a b hab) (u p q hpq) =
      triangle x y a b p q := by
  rw [shortCubic_swap_right, cubic_uuv, triangle_swap_last x y p q a b hxy hpq hab]

private theorem cubic_vuu (x y a b p q : Omega)
    (hxy : x ≠ y) (hab : a ≠ b) (hpq : p ≠ q) :
    shortCubic sourceLatticeComparison (v x y hxy) (u a b hab) (u p q hpq) =
      triangle x y a b p q := by
  rw [shortCubic_swap_left, cubic_uvu, triangle_swap_first a b x y p q hab hxy hpq]

/-- The all-short source table, including every degenerate endpoint and unequal-axis case. -/
theorem shortCubic_shortPair (b c d : Bool) (x y u v p q : Omega)
    (hxy : x ≠ y) (huv : u ≠ v) (hpq : p ≠ q) :
    Griess.shortCubic LocalC.sourceLatticeComparison
      (shortPair b x y hxy) (shortPair c u v huv) (shortPair d p q hpq) =
      if b = c ∧ c = d then 4 * triangle x y u v p q else 0 := by
  cases b <;> cases c <;> cases d <;>
    simp only [shortPair, Bool.false_eq_true, if_false, if_true, wPlus, wMinus,
      map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply,
      cubic_vvv, cubic_uvv, cubic_vuv, cubic_vvu, cubic_uuv, cubic_uvu, cubic_vuu, cubic_uuu] <;>
    simp <;> ring

/-- Application to the literal source short inclusions in the fixed Griess carrier. -/
theorem griessBeta_shortPair (b c d : Bool) (x y u v p q : Omega)
    (hxy : x ≠ y) (huv : u ≠ v) (hpq : p ≠ q) :
    Sporadic.Monster.griessBeta
      (LocalC.shortInclusion LocalC.sourceLatticeComparison (shortPair b x y hxy))
      (LocalC.shortInclusion LocalC.sourceLatticeComparison (shortPair c u v huv))
      (LocalC.shortInclusion LocalC.sourceLatticeComparison (shortPair d p q hpq)) =
      if b = c ∧ c = d then 4 * triangle x y u v p q else 0 := by
  exact (sourceBeta_RRR sourceLatticeComparison _ _ _).trans
    (shortCubic_shortPair b c d x y u v p q hxy huv hpq)

end Sporadic.Monster.Construction.NMonomial.EAction.SourceCubic
