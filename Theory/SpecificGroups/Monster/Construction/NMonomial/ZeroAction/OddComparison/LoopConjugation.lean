module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.OddComparison.Stability
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.QuadraticQuotient
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.TrialityGenerators.Relations

/-!
# Loop conjugation on the signed odd short family

The polar form of the literal extraspecial quotient proves the first
loop-family commutator and its conjugation action, including the central sign.
The fixed odd representation transfers this identity to actual signed vectors.

For the second family, direct collection at the loop identity gives the sign
`epsilon_x(e) + P(e)`. Thus the proposed formula with only `epsilon_x(e)`
is false for the existing definitions: the sum of Golay basis words 0 and 8
has weight twelve and gives the opposite central lift at every point. The
counterexample is in `Q1Image`, not merely in its lattice-class quotient.
This module does not assert the general second-family clause of 29.6.

Source: Aschbacher, *Sporadic Groups*, 29.6(1),(2), printed p. 156 (PDF p. 84),
27.8(3), printed p. 150 (PDF p. 81), and Section 14, printed pp. 58--61
(PDF pp. 35--36). The permutations and source word agree with the scanned
Section 14 and 27.8 definitions; reversing right-action products gives
conjugation `g * r * g⁻¹`. The extra quarter-weight sign is obtained from
14.2's odd-automorphism collection and inverse formulas. The private
collection calculation follows the existing project proof in
`LocalC/LatticeComparison/TrialityGenerators.lean`, keeping its boundary intact.
-/

@[expose] public section
open Atlas.Codes Atlas.Fischer Atlas.Lattices
open Sporadic.Monster.Construction LocalC ShortFamilies TrialitySpin
open scoped commutatorElement
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction

private theorem pairing_point (x : Omega) (d : golay) :
    cocodePairing d (Submodule.Quotient.mk (pointWord x)) = d.val x := by
  simp [cocodePairing, cocodeDualEquiv_mk, binaryDot_apply, pointWord, Pi.single_apply]

private theorem parity_point (x : Omega) :
    cocodeParity (Submodule.Quotient.mk (pointWord x)) = 1 := by
  simp [cocodeParity_mk, binaryDot_apply, pointWord, Pi.single_apply, allOnes]

private theorem polar_loop (b d : ParkerLoop) :
    coordinatePolar (q1ImageCoordinates (loopImage b)).toAdd
      (q1ImageCoordinates (loopImage d)).toAdd = golayHalfOverlap b.1 d.1 := by
  simp [loopImage, q1Coordinates_param, q1WordCoordinates, coordinatePolar]

private theorem polar_point (x : Omega) (d : ParkerLoop) :
    coordinatePolar (q1ImageCoordinates (cocodeImage (pointWord x))).toAdd
      (q1ImageCoordinates (loopImage d)).toAdd = d.1.val x + golayQuarterWeight d.1 := by
  simp [loopImage, cocodeImage, q1Coordinates_param, q1WordCoordinates, coordinatePolar,
    loopOne, pairing_point, parity_point]

/-- Aschbacher 29.6(1), retaining the actual central sign in `N/K`. -/
theorem rOddElement_commutator_loopImage (x : Omega) (b d : ParkerLoop) :
    ⁅rOddElement x b, loopImage d⁆ = q1ImageCenterGenerator ^
      (d.1.val x + golayQuarterWeight d.1 + golayHalfOverlap d.1 b.1).val := by
  rw [Q1Image_commutator_coordinates]
  apply congrArg (fun s : ParkerBit => q1ImageCenterGenerator ^ s.val)
  simp only [rOddElement, map_mul, map_pow, toAdd_mul,
    toAdd_pow, coordinatePolar_add_left]
  rcases bit_cases (b.1.val x) with h | h <;>
    simp only [h, ZMod.val_zero, ZMod.val_one, zero_nsmul, one_nsmul,
      polar_loop, polar_point, parkerOmega, golayHalfOverlap_one,
      coordinatePolar_zero_left, add_zero] <;>
    rw [golayHalfOverlap_symmetric b.1 d.1] <;> ac_rfl


private theorem image_conjugation_val (g : N1) (q : Q1Image) :
    (q1ImageConjugation g q).val =
      nQuotientMap g.val * q.val * (nQuotientMap g.val)⁻¹ := rfl

private theorem conjugation_psi1_inner (d : ParkerLoop) (q : Q1Image) :
    q1ImageConjugation ⟨psi1N d, psi1N_mem_N1 d⟩ q =
      loopImage d * q * (loopImage d)⁻¹ := by
  apply Subtype.ext
  simp only [image_conjugation_val, Subgroup.coe_mul, Subgroup.coe_inv, loopImage_val]

/-- The first loop generator acts on the literal signed odd lift. -/
theorem rOddElement_conjugation_psi1 (x : Omega) (b d : ParkerLoop) :
    q1ImageConjugation ⟨psi1N d, psi1N_mem_N1 d⟩ (rOddElement x b) =
      rOddElement x (parkerSign
        (d.1.val x + golayQuarterWeight d.1 + golayHalfOverlap d.1 b.1) b) := by
  rw [rOddElement_sign, conjugation_psi1_inner]
  have hc : ⁅loopImage d, rOddElement x b⁆ = ⁅rOddElement x b, loopImage d⁆ := by
    rw [Q1Image_commutator_coordinates, Q1Image_commutator_coordinates, coordinatePolar_comm]
  rw [← rOddElement_commutator_loopImage, ← hc, commutatorElement_def]
  group

open TrialityGeneratorCalculation

private theorem point_odd (x : Omega) :
    (parkerCocodeStandard (Submodule.Quotient.mk (pointWord x))).val parkerOmega ≠
      parkerOmega := by
  rw [parkerCocodeStandard_apply, pairing_point]
  intro h
  have := congrArg Prod.snd h
  change (0 : ParkerBit) + 1 = 0 at this
  exact one_ne_zero this

private theorem conjugation_psi2_point_N (x : Omega) (e : ParkerLoop) :
    psi2N e * psiAut1N (parkerCocodeStandard (Submodule.Quotient.mk (pointWord x))) *
        (psi2N e)⁻¹ =
      psiAut1N (parkerCocodeStandard (Submodule.Quotient.mk (pointWord x))) *
        psi3N (0,e.1.val x) * psi1N e := by
  let α := parkerCocodeStandard (Submodule.Quotient.mk (pointWord x))
  have hs : α.val.symm e = α.val e := by
    apply α.val.injective
    simp [α, parkerCocodeStandard_apply, add_assoc]
  have hm := aut_psi3_odd α (point_odd x) (loopInverse (α.val.symm e))
  rw [loopInverse_inverse, Equiv.apply_symm_apply, hs] at hm
  have ha : α.val e = parkerSign (e.1.val x) e := by
    rw [parkerCocodeStandard_apply, pairing_point]
    rfl
  rw [ha, loopInverse_sign, psi3_sign] at hm
  have hd : psi3N (loopInverse e) * psi2N (loopInverse e) = psi1N e := by
    have h := psi3N_mul_psi2N_mul_psi1N (loopInverse e)
    calc
      _ = (psi1N (loopInverse e))⁻¹ := eq_inv_of_mul_eq_one_left h
      _ = psi1N e := by rw [psi1N_inv, loopInverse_inverse]
  change psi2N e * psiAut1N α * (psi2N e)⁻¹ = _
  rw [← hm, psi2_inv]
  simpa only [mul_assoc] using congrArg
    (fun y : N => psiAut1N α * (psi3N (0,e.1.val x) * y)) hd

private theorem second_sign_image (s : ParkerBit) :
    nQuotientMap (psi2N (0,s)) = (loopImage parkerOmega ^ s.val).val := by
  rcases bit_cases s with rfl | rfl
  · change nQuotientMap (psi2N loopOne) = _
    rw [psi2_one, map_one]
    rfl
  · have h := congrArg nQuotientMap k1_eq_z2_mul_psi1_omega
    rw [(nQuotientMap_eq_one k1).mpr ((mem_K_iff k1).mpr (by simp)), map_mul] at h
    have hi := eq_inv_of_mul_eq_one_left h.symm
    rw [← map_inv, psi1N_inv, loopInverse_omega] at hi
    exact hi.trans (loopImage_val parkerOmega).symm

private theorem conjugation_psi2_point (x : Omega) (e : ParkerLoop) :
    q1ImageConjugation ⟨psi2N e, psi2N_mem_N1 e⟩ (cocodeImage (pointWord x)) =
      rOddElement x (parkerSign (e.1.val x + golayQuarterWeight e.1) e) := by
  let α := parkerCocodeStandard (Submodule.Quotient.mk (pointWord x))
  have ha (d : ParkerLoop) : α.val d = parkerSign (d.1.val x) d := by
    rw [parkerCocodeStandard_apply, pairing_point]
    rfl
  have ht := aut_psi3_odd α (point_odd x) (0,e.1.val x)
  have hl := aut_psi1_odd α (point_odd x) e
  have hi : α.val (loopInverse (0,e.1.val x)) = (0,e.1.val x) := by
    simp [ha, loopInverse, parkerSign]
  rw [hi] at ht
  rw [ha, loopInverse, parkerSign_add] at hl
  change psiAut1N α * psi1N e =
    psi1N (parkerSign (e.1.val x + golayQuarterWeight e.1) e) * psiAut1N α at hl
  have hp : psi2N (0,e.1.val x) * psi1N (parkerSign
        (e.1.val x + golayQuarterWeight e.1) e) =
      psi1N (parkerSign (e.1.val x + golayQuarterWeight e.1) e) * psi2N (0,e.1.val x) := by
    rcases bit_cases (e.1.val x) with h | h
    · rw [h]; change psi2N loopOne * _ = _ * psi2N loopOne
      rw [psi2_one, one_mul, mul_one]
    · rw [h]
      apply Subtype.ext
      ext ⟨a,b,c⟩ : 1
      change z2 (psi1 _ (a,b,c)) = psi1 _ (z2 (a,b,c))
      simp
  have hn := conjugation_psi2_point_N x e
  change _ = psiAut1N α * psi3N (0,e.1.val x) * psi1N e at hn
  rw [ht, mul_assoc (psi2N (0,e.1.val x)), hl,
    ← mul_assoc (psi2N (0,e.1.val x)), hp] at hn
  apply Subtype.ext
  rw [image_conjugation_val, cocodeImage_val]
  change nQuotientMap (psi2N e) * nQuotientMap (psiAut1N α) *
    (nQuotientMap (psi2N e))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, hn, map_mul, map_mul, second_sign_image]
  simp only [rOddElement, Subgroup.coe_mul, loopImage_val, cocodeImage_val]
  rfl


private theorem loopImage_one : loopImage loopOne = 1 := by
  apply Subtype.ext
  rw [loopImage_val, psi1_one, map_one]
  rfl

@[simp] private theorem rOddElement_loopOne (x : Omega) :
    rOddElement x loopOne = cocodeImage (pointWord x) := by
  rw [rOddElement, loopImage_one]
  change 1 * loopImage parkerOmega ^ 0 * cocodeImage (pointWord x) = _
  rw [pow_zero, mul_one, one_mul]

/-- Exact second-family action at the loop identity, including the quarter-weight sign. -/
theorem rOddElement_conjugation_psi2_loopOne (x : Omega) (e : ParkerLoop) :
    q1ImageConjugation ⟨psi2N e, psi2N_mem_N1 e⟩ (rOddElement x loopOne) =
      rOddElement x (parkerSign (e.1.val x + golayQuarterWeight e.1) e) := by
  rw [rOddElement_loopOne]
  exact conjugation_psi2_point x e

/-- For quarter-weight one, the proposed second-family formula is the opposite lift. -/
theorem rOddElement_conjugation_psi2_loopOne_ne (x : Omega) (e : ParkerLoop)
    (he : golayQuarterWeight e.1 = 1) :
    q1ImageConjugation ⟨psi2N e, psi2N_mem_N1 e⟩ (rOddElement x loopOne) ≠
      rOddElement x (parkerSign (e.1.val x) (parkerLoopMultiply e loopOne)) := by
  rw [rOddElement_conjugation_psi2_loopOne, he]
  have hm : parkerLoopMultiply e loopOne = e := parkerLoopMultiply_one_right e
  rw [hm, add_comm (e.1.val x), ← parkerSign_add, rOddElement_sign]
  simp only [ZMod.val_one, pow_one]
  intro h
  exact q1ImageCenterGenerator_ne_one (mul_right_cancel (h.trans (one_mul _).symm))

/-- A weight-twelve codeword refutes the proposed formula at every marked point. -/
theorem exists_rOddElement_conjugation_psi2_ne (x : Omega) :
    ∃ e : ParkerLoop,
      q1ImageConjugation ⟨psi2N e, psi2N_mem_N1 e⟩ (rOddElement x loopOne) ≠
        rOddElement x (parkerSign (e.1.val x) (parkerLoopMultiply e loopOne)) := by
  refine ⟨(golayBasis 0 + golayBasis 8, 0),
    rOddElement_conjugation_psi2_loopOne_ne x _ ?_⟩
  change golayQuarterWeight (golayBasis 0 + golayBasis 8) = 1
  unfold golayQuarterWeight
  rw [Submodule.coe_add, golayBasis_coe, golayBasis_coe]
  decide


/-- The first-family conjugation gives the actual signed vector action. -/
theorem oddRepresentation_vector_psi1 (x : Omega) (b d : ParkerLoop) :
    oddRepresentation ⟨psi1N d, psi1N_mem_N1 d⟩ (zeroOdd x b).1 =
      (zeroOdd x (parkerSign
        (d.1.val x + golayQuarterWeight d.1 + golayHalfOverlap d.1 b.1) b)).1 :=
  oddRepresentation_vector_of_conjugation _ _ _ _ _ (rOddElement_conjugation_psi1 x b d)

/-- The exact basepoint calculation also determines the signed vector image. -/
theorem oddRepresentation_vector_psi2_loopOne (x : Omega) (e : ParkerLoop) :
    oddRepresentation ⟨psi2N e, psi2N_mem_N1 e⟩ (zeroOdd x loopOne).1 =
      (zeroOdd x (parkerSign (e.1.val x + golayQuarterWeight e.1) e)).1 :=
  oddRepresentation_vector_of_conjugation _ _ _ _ _ (rOddElement_conjugation_psi2_loopOne x e)

end Sporadic.Monster.Construction.NMonomial.ZeroAction
