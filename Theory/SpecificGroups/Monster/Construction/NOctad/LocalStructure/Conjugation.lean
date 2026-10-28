module

public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Parameters
public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Transport

/-!
# The actual octad conjugation formulas

The three identities of Aschbacher 29.12 are equalities of the source words
in the actual extraspecial group `Q1Image`. The first loop family is computed
from the proved commutator form. The second uses the Section 14 collection
law: its second sign generator becomes the omega image in `N/K`, and its
third sign generator contributes both omega and the central sign. The proved
half-weight identity then collects the translated subset exactly.

Standard automorphisms transport both the loop and subset. For odd standard
automorphisms, the octad loop is still an involution, but omega changes sign;
its exponent contributes the additional half-weight central sign. The fixed
local representation transfers all four equalities to actual signed vectors.
Sign changes and subset complementation are retained as element and vector
identities, so none of these statements discards the central sign by passing
to lattice classes.

Source: Michael Aschbacher, *Sporadic Groups*, Lemma 29.12, printed p. 160
(PDF p. 86, left page), with 14.2, printed pp. 59–60, and the definition in
27.8, printed p. 150. Products reverse the source's right-action order;
conjugation here is `g * q * g⁻¹`. Collection proofs use the project's public
triality relations without changing their private implementation boundaries.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NOctad.LocalStructure.Conjugation
open LocalC LocalC.ShortFamilies TrialitySpin LocalC.TrialityGeneratorCalculation
open Atlas.Codes Atlas.Fischer Atlas.Lattices
open scoped commutatorElement

private theorem conjugation_val (g : N1) (q : Q1Image) :
    (q1ImageConjugation g q).val =
      nQuotientMap g.val * q.val * (nQuotientMap g.val)⁻¹ := rfl

private theorem cocode_even (J : BinaryWord) (hJ : Even (hammingNorm J)) :
    (parkerCocodeStandard (Submodule.Quotient.mk J)).val parkerOmega = parkerOmega := by
  have h : cocodeParity (Submodule.Quotient.mk J) = 0 := by
    rw [cocodeParity_mk]
    simpa only [binaryDot_apply, allOnes, one_mul] using (even_weight_iff J).mp hJ
  simp [parkerOmega, cocodePairing_one, h]

private theorem pairing_mk (J : BinaryWord) (d : golay) :
    cocodePairing d (Submodule.Quotient.mk J) = binaryDot J d.val := by
  rw [cocodePairing, cocodeDualEquiv_mk, binaryDot_symmetric]

private theorem conjugation_loop_even (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (d : ParkerLoop) :
    q1ImageConjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (loopImage d) =
      loopImage (α.val d) := by
  apply Subtype.ext
  rw [conjugation_val, loopImage_val, loopImage_val]
  change nQuotientMap (psiAut1N α) * nQuotientMap (psi1N d) *
    (nQuotientMap (psiAut1N α))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, aut_psi1_even α hα, mul_inv_cancel_right]

private theorem conjugation_loop_odd (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (d : ParkerLoop) :
    q1ImageConjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (loopImage d) =
      loopImage (α.val (loopInverse d)) := by
  apply Subtype.ext
  rw [conjugation_val, loopImage_val, loopImage_val]
  change nQuotientMap (psiAut1N α) * nQuotientMap (psi1N d) *
    (nQuotientMap (psiAut1N α))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, aut_psi1_odd α hα, mul_inv_cancel_right]

private theorem pairing_permutation (σ : Mathieu24CodeModel) (v : golay) (c : Cocode) :
    cocodePairing (parkerCodeEquiv σ v) (sourceCocodePermutation σ c) =
      cocodePairing v c := by
  obtain ⟨J,rfl⟩ := Submodule.Quotient.mk_surjective golay c
  rw [sourceCocodePermutation_mk, cocodePairing, cocodePairing,
    cocodeDualEquiv_mk, cocodeDualEquiv_mk]
  exact Equiv.sum_comp σ.val.symm (fun p => v.val p * J p)

private theorem conjugation_cocode (α : ParkerStandardGroup) (J : BinaryWord) :
    q1ImageConjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (cocodeImage J) =
      cocodeImage (coordinatePermutation (parkerStandardProjection α).val J) := by
  have h (c : Cocode) : α * parkerCocodeStandard c =
      parkerCocodeStandard (sourceCocodePermutation (parkerStandardProjection α) c) * α := by
    apply Subtype.ext
    ext d : 1
    change α.val (parkerSign (cocodePairing d.1 c) d) =
      parkerSign (cocodePairing (α.val d).1
        (sourceCocodePermutation (parkerStandardProjection α) c)) (α.val d)
    rw [parkerStandard_preserves_sign, parkerStandardProjection_spec, pairing_permutation]
  have hm := congrArg psiAut1N (h (Submodule.Quotient.mk J))
  rw [aut_mul, aut_mul, sourceCocodePermutation_mk] at hm
  apply Subtype.ext
  rw [conjugation_val, cocodeImage_val, cocodeImage_val]
  change nQuotientMap (psiAut1N α) * nQuotientMap (psiAut1N _) *
    (nQuotientMap (psiAut1N α))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, hm, mul_inv_cancel_right]

private theorem cocodeImage_add (J K : BinaryWord) :
    cocodeImage (J + K) = cocodeImage J * cocodeImage K := by
  have h : parkerCocodeStandard ((Submodule.Quotient.mk J : Cocode) + Submodule.Quotient.mk K) =
      parkerCocodeStandard (Submodule.Quotient.mk J) *
        parkerCocodeStandard (Submodule.Quotient.mk K) :=
    parkerCocodeHom.map_mul (Multiplicative.ofAdd (Submodule.Quotient.mk J))
      (Multiplicative.ofAdd (Submodule.Quotient.mk K))
  apply Subtype.ext
  simp only [Subgroup.coe_mul, cocodeImage_val]
  rw [Submodule.Quotient.mk_add, h, aut_mul, map_mul]

private theorem omega_square : loopImage parkerOmega ^ 2 = 1 := by
  apply Subtype.ext
  simp only [Subgroup.coe_pow, loopImage_val, Subgroup.coe_one, ← map_pow]
  have h : psi1N parkerOmega ^ 2 = 1 := by
    apply Subtype.ext
    ext ⟨a,b,c⟩ : 1
    change psi1 parkerOmega (psi1 parkerOmega (a,b,c)) = (a,b,c)
    simp [psi1_apply]
  rw [h, map_one]

private theorem second_sign_image (s : ParkerBit) :
    nQuotientMap (psi2N (0,s)) = (loopImage parkerOmega ^ s.val).val := by
  have hs : s = 0 ∨ s = 1 := by revert s; decide
  rcases hs with rfl | rfl
  · change nQuotientMap (psi2N loopOne) = _
    rw [psi2_one, map_one]
    rfl
  · have h : psi2N (0,1) = k1 * psi1N parkerOmega := by
      apply Subtype.ext
      ext ⟨a,b,c⟩ : 1
      change z2 (a,b,c) = k1.val (psi1 parkerOmega (a,b,c))
      simp [k1_apply, psi1_apply]
    rw [h, map_mul, (nQuotientMap_eq_one k1).mpr ((mem_K_iff _).mpr (by simp)), one_mul]
    exact (loopImage_val parkerOmega).symm

private theorem third_sign_image (s : ParkerBit) :
    nQuotientMap (psi3N (0,s)) =
      (q1ImageCenterGenerator ^ s.val * loopImage parkerOmega ^ s.val).val := by
  have hs : s = 0 ∨ s = 1 := by revert s; decide
  have h : psi3N (0,s) = psi1N (0,s) * psi2N (0,s) := by
    rcases hs with rfl | rfl
    · change psi3N loopOne = psi1N loopOne * psi2N loopOne
      rw [psi1_one, psi2_one, one_mul]
      apply Subtype.ext
      ext ⟨a,b,c⟩ : 1
      simp [psi3N]
    · apply Subtype.ext
      ext ⟨a,b,c⟩ : 1
      change z3 (a,b,c) = z1 (z2 (a,b,c))
      simp
  have hz : nQuotientMap (psi1N (0,s)) = (q1ImageCenterGenerator ^ s.val).val := by
    rcases hs with rfl | rfl
    · change nQuotientMap (psi1N loopOne) = _
      rw [psi1_one, map_one]
      rfl
    · rfl
  rw [h, map_mul, hz, second_sign_image]
  rfl

private theorem conjugation_psi1_inner (d : ParkerLoop) (q : Q1Image) :
    q1ImageConjugation ⟨psi1N d, psi1N_mem_N1 d⟩ q =
      loopImage d * q * (loopImage d)⁻¹ := by
  apply Subtype.ext
  simp only [conjugation_val, Subgroup.coe_mul, Subgroup.coe_inv, loopImage_val]

private theorem inner_eq_polar (x y : Q1Image) :
    x * y * x⁻¹ = q1ImageCenterGenerator ^
      (coordinatePolar (q1ImageCoordinates x).toAdd (q1ImageCoordinates y).toAdd).val * y := by
  rw [← Q1Image_commutator_coordinates, commutatorElement_def]
  group

private theorem conjugation_psi1_loop (d c : ParkerLoop) :
    q1ImageConjugation ⟨psi1N d, psi1N_mem_N1 d⟩ (loopImage c) =
      q1ImageCenterGenerator ^ (golayHalfOverlap d.1 c.1).val * loopImage c := by
  rw [conjugation_psi1_inner, inner_eq_polar]
  congr 2
  simp [loopImage, q1Coordinates_param, q1WordCoordinates, coordinatePolar]

private theorem conjugation_psi1_cocode (d : ParkerLoop) (J : BinaryWord)
    (hJ : Even (hammingNorm J)) :
    q1ImageConjugation ⟨psi1N d, psi1N_mem_N1 d⟩ (cocodeImage J) =
      q1ImageCenterGenerator ^ (binaryDot J d.1.val).val * cocodeImage J := by
  have h : cocodeParity (Submodule.Quotient.mk J) = 0 := by
    rw [cocodeParity_mk]
    simpa only [binaryDot_apply, allOnes, one_mul] using (even_weight_iff J).mp hJ
  rw [conjugation_psi1_inner, inner_eq_polar]
  have hp : coordinatePolar (q1ImageCoordinates (loopImage d)).toAdd
      (q1ImageCoordinates (cocodeImage J)).toAdd = binaryDot J d.1.val := by
    simp [loopImage, cocodeImage, q1Coordinates_param, q1WordCoordinates,
      coordinatePolar, loopOne, h, pairing_mk]
  rw [hp]

private theorem conjugation_psi2_cocode (e : ParkerLoop) (J : BinaryWord)
    (hJ : Even (hammingNorm J)) :
    q1ImageConjugation ⟨psi2N e, psi2N_mem_N1 e⟩ (cocodeImage J) =
      cocodeImage J * loopImage parkerOmega ^ (binaryDot J e.1.val).val := by
  let α := parkerCocodeStandard (Submodule.Quotient.mk J)
  have hs : α.val.symm e = α.val e := by
    apply α.val.injective
    simp [α, parkerCocodeStandard_apply, add_assoc]
  have hm := aut_psi2_even α (cocode_even J hJ) (α.val.symm e)
  rw [Equiv.apply_symm_apply, hs] at hm
  have ha : α.val e = parkerSign (binaryDot J e.1.val) e := by
    change parkerSign (cocodePairing e.1 (Submodule.Quotient.mk J)) e = _
    rw [pairing_mk]
  rw [ha, psi2_sign] at hm
  have hc : psi2N e * psiAut1N α * (psi2N e)⁻¹ =
      psiAut1N α * psi2N (0,binaryDot J e.1.val) := by
    rw [← hm]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  apply Subtype.ext
  rw [conjugation_val, cocodeImage_val, Subgroup.coe_mul, cocodeImage_val]
  change nQuotientMap (psi2N e) * nQuotientMap (psiAut1N α) *
    (nQuotientMap (psi2N e))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, hc, map_mul, second_sign_image]

private theorem conjugation_psi2_loop (e c : ParkerLoop) :
    q1ImageConjugation ⟨psi2N e, psi2N_mem_N1 e⟩ (loopImage c) =
      cocodeImage (e.1.val * c.1.val) *
        (q1ImageCenterGenerator ^ (golayHalfOverlap e.1 c.1).val *
          loopImage parkerOmega ^ (golayHalfOverlap e.1 c.1).val) * loopImage c := by
  apply Subtype.ext
  rw [conjugation_val, loopImage_val]
  change nQuotientMap (psi2N e) * nQuotientMap (psi1N c) *
    (nQuotientMap (psi2N e))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, psi2N_conj_psi1N, map_mul, map_mul,
    third_sign_image]
  simp only [Subgroup.coe_mul, loopImage_val, cocodeImage_val]
  rfl

private theorem central_commute (q : Q1Image) : Commute q1ImageCenterGenerator q :=
  (Subgroup.mem_center_iff.mp centerGenerator_mem q).symm

private theorem bit_pow_add {G : Type*} [Group G] (x : G) (hx : x ^ 2 = 1)
    (s t : ParkerBit) : x ^ (s + t).val = x ^ s.val * x ^ t.val := by
  have hs : s = 0 ∨ s = 1 := by revert s; decide
  have ht : t = 0 ∨ t = 1 := by revert t; decide
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    simp only [zero_add, add_zero, CharTwo.add_self_eq_zero, ZMod.val_zero,
      ZMod.val_one, pow_zero, pow_one, one_mul, mul_one]
  simpa only [pow_two] using hx.symm

private theorem pow_bit (x : Q1Image) (hx : x ^ 2 = 1) (n : ℕ) :
    x ^ n = x ^ (n : ParkerBit).val := by
  rw [pow_eq_pow_mod n hx]
  rfl

private theorem omega_cocode_commute (J : BinaryWord) (hJ : Even (hammingNorm J)) :
    Commute (loopImage parkerOmega) (cocodeImage J) := by
  have he : binaryDot J parkerOmega.1.val = 0 := by
    change binaryDot J allOnes = 0
    rw [binaryDot_symmetric]
    simpa only [binaryDot_apply, allOnes, one_mul] using (even_weight_iff J).mp hJ
  have h := conjugation_psi1_cocode parkerOmega J hJ
  rw [conjugation_psi1_inner, he] at h
  simp only [ZMod.val_zero, pow_zero, one_mul] at h
  exact mul_inv_eq_iff_eq_mul.mp h

private theorem conjugation_psi2_omega (e : ParkerLoop) :
    q1ImageConjugation ⟨psi2N e, psi2N_mem_N1 e⟩ (loopImage parkerOmega) =
      loopImage parkerOmega := by
  rw [conjugation_psi2_loop]
  have hc : cocodeImage (e.1.val * parkerOmega.1.val) = 1 := by
    have he : e.1.val * parkerOmega.1.val = e.1.val := by ext i; simp [parkerOmega, golayOne, allOnes]
    rw [he]
    apply Subtype.ext
    rw [cocodeImage_val, (Submodule.Quotient.mk_eq_zero golay).mpr e.1.prop]
    change nQuotientMap (psiAut1N (parkerCocodeHom 1)) = 1
    rw [map_one, aut_one, map_one]
  rw [hc]
  simp only [parkerOmega, golayHalfOverlap_one_right, ZMod.val_zero, pow_zero, mul_one, one_mul]

/-- Lemma 29.12(1), on actual extraspecial elements. -/
theorem standard (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (p : OctadParameters) :
    q1ImageConjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (rOctad p).val =
      (rOctad (standardParameters α p)).val := by
  change q1ImageConjugation _ (rOctadElement p.c p.J) = _
  simp only [rOctadElement, map_mul, map_pow, conjugation_loop_even α hα,
    hα, conjugation_cocode, rOctad_val, standardParameters]
  rw [coordinatePermutation_weight]

/-- Lemma 29.12(2), retaining both epsilon and half-intersection signs. -/
theorem psi1 (d : ParkerLoop) (p : OctadParameters) :
    q1ImageConjugation ⟨psi1N d, psi1N_mem_N1 d⟩ (rOctad p).val =
      (rOctad (psi1Parameters d p)).val := by
  have ho : q1ImageConjugation ⟨psi1N d, psi1N_mem_N1 d⟩ (loopImage parkerOmega) =
      loopImage parkerOmega := by
    simp [conjugation_psi1_loop, parkerOmega]
  change q1ImageConjugation _ (rOctadElement p.c p.J) =
    rOctadElement (parkerSign (binaryDot p.J d.1.val + golayHalfOverlap p.c.1 d.1) p.c) p.J
  rw [rOctadElement_sign]
  simp only [rOctadElement, map_mul, map_pow, ho, conjugation_psi1_cocode d p.J p.even,
    conjugation_psi1_loop, bit_pow_add _ q1ImageCenterGenerator_sq,
    golayHalfOverlap_symmetric d.1 p.c.1]
  have he := (central_commute (cocodeImage p.J)).pow_left (binaryDot p.J d.1.val).val
  have hc := (central_commute (loopImage p.c)).pow_left (golayHalfOverlap p.c.1 d.1).val
  have hec := (central_commute (loopImage p.c)).pow_left (binaryDot p.J d.1.val).val
  calc
    _ = loopImage parkerOmega ^ (hammingNorm p.J / 2) *
        (cocodeImage p.J * (q1ImageCenterGenerator ^ (binaryDot p.J d.1.val).val *
          (loopImage p.c * q1ImageCenterGenerator ^ (golayHalfOverlap p.c.1 d.1).val))) := by
      rw [he.eq, hc.eq]
      simp only [mul_assoc]
    _ = _ := by rw [← mul_assoc _ (loopImage p.c), hec.eq]; simp only [mul_assoc]

/-- Lemma 29.12(3), in the literal left-conjugation convention. -/
theorem psi2 (e : ParkerLoop) (p : OctadParameters) :
    q1ImageConjugation ⟨psi2N e, psi2N_mem_N1 e⟩ (rOctad p).val =
      (rOctad (psi2Parameters e p)).val := by
  let O := loopImage parkerOmega
  let Z := q1ImageCenterGenerator
  let A := cocodeImage p.J
  let B := cocodeImage (p.c.1.val * e.1.val)
  let C := loopImage p.c
  let s := golayHalfOverlap e.1 p.c.1
  let t := binaryDot p.J e.1.val
  let n := hammingNorm p.J / 2
  have hB : Even (hammingNorm (p.c.1.val * e.1.val)) := by
    apply even_iff_two_dvd.mpr
    have h := golay_overlap_two_dvd p.c.1 e.1
    simpa only [hammingNorm, overlap, Pi.mul_apply, mul_ne_zero_iff] using h
  have hoA : Commute O A := omega_cocode_commute p.J p.even
  have hoB : Commute O B := omega_cocode_commute _ hB
  have hzO : Commute Z O := central_commute _
  have hzC : Commute Z C := central_commute _
  have hp : O ^ (hammingNorm (psi2Parameters e p).J / 2) = O ^ n * O ^ t.val * O ^ s.val := by
    rw [pow_bit O omega_square, translatedSubset_half_weight,
      golayHalfOverlap_symmetric p.c.1 e.1]
    change O ^ ((n : ParkerBit) + s + t).val = _
    rw [bit_pow_add O omega_square, bit_pow_add O omega_square,
      ← pow_bit O omega_square]
    rw [mul_assoc, (Commute.refl O).pow_pow s.val t.val |>.eq, ← mul_assoc]
  change q1ImageConjugation _ (rOctadElement p.c p.J) =
    rOctadElement (parkerSign s p.c) (psi2Parameters e p).J
  rw [rOctadElement_sign]
  simp only [rOctadElement, map_mul, map_pow]
  rw [conjugation_psi2_omega, conjugation_psi2_cocode e p.J p.even, conjugation_psi2_loop]
  rw [mul_comm e.1.val p.c.1.val, show (psi2Parameters e p).J = p.J + p.c.1.val * e.1.val from rfl,
    cocodeImage_add]
  change O ^ n * (A * O ^ t.val) * (B * (Z ^ s.val * O ^ s.val) * C) =
    O ^ (hammingNorm (psi2Parameters e p).J / 2) * (A * B) * C * Z ^ s.val
  rw [hp]
  have htA := hoA.pow_left t.val
  have hsAB := (hoA.mul_right hoB).pow_left s.val
  have hsOC := ((hzO.pow_pow s.val s.val).mul_right (hzC.pow_left s.val))
  calc
    _ = O ^ n * (O ^ t.val * A) * (B * (O ^ s.val * C * Z ^ s.val)) := by
      rw [htA.eq]
      simp only [mul_assoc]
      rw [hsOC.eq]
      simp only [mul_assoc]
    _ = O ^ n * O ^ t.val * (A * B) * O ^ s.val * C * Z ^ s.val := by
      simp only [mul_assoc]
    _ = _ := by rw [mul_assoc (O ^ n * O ^ t.val) (A * B), ← hsAB.eq]; simp only [mul_assoc]

/-- Odd standard automorphisms contribute the omega half-weight sign. -/
theorem standard_odd (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (p : OctadParameters) :
    q1ImageConjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (rOctad p).val =
      (rOctad ((standardParameters α p).sign ((hammingNorm p.J / 2 : ℕ) : ParkerBit))).val := by
  have hi : loopInverse p.c = p.c := by
    have hw : golayQuarterWeight p.c.1 = 0 := by
      rw [golayQuarterWeight, p.octad]
      rfl
    rw [loopInverse, hw, parkerSign_zero]
  have ho : loopInverse parkerOmega = parkerOmega := loopInverse_omega
  change q1ImageConjugation _ (rOctadElement p.c p.J) =
    rOctadElement (parkerSign ((hammingNorm p.J / 2 : ℕ) : ParkerBit) (α.val p.c))
      (coordinatePermutation (parkerStandardProjection α).val p.J)
  rw [rOctadElement_sign]
  simp only [rOctadElement, map_mul, map_pow, conjugation_loop_odd α hα, hi, ho,
    parkerStandard_omega_odd α hα, loopImage_sign, conjugation_cocode]
  rw [coordinatePermutation_weight]
  simp only [ZMod.val_one, pow_one]
  rw [(central_commute (loopImage parkerOmega)).mul_pow]
  rw [pow_bit q1ImageCenterGenerator q1ImageCenterGenerator_sq]
  have h := (central_commute (loopImage parkerOmega ^ (hammingNorm p.J / 2) *
    cocodeImage (coordinatePermutation (parkerStandardProjection α).val p.J) *
    loopImage (α.val p.c))).pow_left ((hammingNorm p.J / 2 : ℕ) : ParkerBit).val
  simpa only [mul_assoc] using h.eq

/-- Transfer of 29.12(1) to the fixed signed-vector representation. -/
theorem vector_standard (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (p : OctadParameters) :
    representation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (vector p) =
      vector (standardParameters α p) :=
  (representation_vector_eq_iff _ _ _).mpr (standard α hα p)

/-- Transfer of 29.12(2) to the fixed signed-vector representation. -/
theorem vector_psi1 (d : ParkerLoop) (p : OctadParameters) :
    representation ⟨psi1N d, psi1N_mem_N1 d⟩ (vector p) =
      vector (psi1Parameters d p) :=
  (representation_vector_eq_iff _ _ _).mpr (psi1 d p)

/-- Transfer of 29.12(3) to the fixed signed-vector representation. -/
theorem vector_psi2 (e : ParkerLoop) (p : OctadParameters) :
    representation ⟨psi2N e, psi2N_mem_N1 e⟩ (vector p) =
      vector (psi2Parameters e p) :=
  (representation_vector_eq_iff _ _ _).mpr (psi2 e p)

/-- The odd formula on actual vectors, including the half-weight sign. -/
theorem vector_standard_odd (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (p : OctadParameters) :
    representation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (vector p) =
      vector ((standardParameters α p).sign ((hammingNorm p.J / 2 : ℕ) : ParkerBit)) :=
  (representation_vector_eq_iff _ _ _).mpr (standard_odd α hα p)

/-- The actual central sign is fixed by every element of `N1`. -/
theorem center_fixed (g : N1) :
    q1ImageConjugation g q1ImageCenterGenerator = q1ImageCenterGenerator := by
  have h : Commute g.val z1N := Subgroup.mem_centralizer_singleton_iff.mp g.prop
  apply Subtype.ext
  change nQuotientMap g.val * nQuotientMap z1N * (nQuotientMap g.val)⁻¹ = nQuotientMap z1N
  rw [← map_inv, ← map_mul, ← map_mul, h.eq, mul_inv_cancel_right]

/-- Changing the loop sign changes the conjugate by the same actual central element. -/
theorem sign (g : N1) (p : OctadParameters) (s : ParkerBit) :
    q1ImageConjugation g (rOctad (p.sign s)).val =
      q1ImageConjugation g (rOctad p).val * q1ImageCenterGenerator ^ s.val := by
  change q1ImageConjugation g (rOctadElement (parkerSign s p.c) p.J) = _
  rw [rOctadElement_sign, map_mul, map_pow, center_fixed]
  rfl

/-- Complementation remains equality of the actual conjugated elements. -/
theorem complement (g : N1) (p : OctadParameters) :
    q1ImageConjugation g (rOctad p.complement).val =
      q1ImageConjugation g (rOctad p).val := by
  rw [rOctad_complement]

/-- Both signed and complemented vector consequences hold in the fixed representation. -/
theorem vector_sign_complement (g : N1) (p : OctadParameters) :
    representation g (vector (p.sign 1)) = -representation g (vector p) ∧
      representation g (vector p.complement) = representation g (vector p) := by
  simp only [vector_sign, vector_complement, map_neg, and_self]

/-- Signed and complemented forms of all three source formulas, on actual group elements. -/
theorem signed_complement (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (d e : ParkerLoop) (p : OctadParameters) (s : ParkerBit) :
    (q1ImageConjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (rOctad (p.sign s)).val =
        (rOctad ((standardParameters α p).sign s)).val ∧
      q1ImageConjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (rOctad p.complement).val =
        (rOctad (standardParameters α p)).val) ∧
    (q1ImageConjugation ⟨psi1N d, psi1N_mem_N1 d⟩ (rOctad (p.sign s)).val =
        (rOctad ((psi1Parameters d p).sign s)).val ∧
      q1ImageConjugation ⟨psi1N d, psi1N_mem_N1 d⟩ (rOctad p.complement).val =
        (rOctad (psi1Parameters d p)).val) ∧
    (q1ImageConjugation ⟨psi2N e, psi2N_mem_N1 e⟩ (rOctad (p.sign s)).val =
        (rOctad ((psi2Parameters e p).sign s)).val ∧
      q1ImageConjugation ⟨psi2N e, psi2N_mem_N1 e⟩ (rOctad p.complement).val =
        (rOctad (psi2Parameters e p)).val) := by
  simp only [← standardParameters_sign, ← psi1Parameters_sign, ← psi2Parameters_sign,
    standard α hα, psi1, psi2, rOctad_complement, and_self]

/-- The signed/complement identities specialize to all three actual vector actions. -/
theorem vector_signed_complement (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (d e : ParkerLoop) (p : OctadParameters) :
    (representation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (vector (p.sign 1)) =
        -vector (standardParameters α p) ∧
      representation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (vector p.complement) =
        vector (standardParameters α p)) ∧
    (representation ⟨psi1N d, psi1N_mem_N1 d⟩ (vector (p.sign 1)) =
        -vector (psi1Parameters d p) ∧
      representation ⟨psi1N d, psi1N_mem_N1 d⟩ (vector p.complement) =
        vector (psi1Parameters d p)) ∧
    (representation ⟨psi2N e, psi2N_mem_N1 e⟩ (vector (p.sign 1)) =
        -vector (psi2Parameters e p) ∧
      representation ⟨psi2N e, psi2N_mem_N1 e⟩ (vector p.complement) =
        vector (psi2Parameters e p)) := by
  simp only [vector_sign, vector_complement, map_neg, vector_standard α hα,
    vector_psi1, vector_psi2, and_self]

/-- The odd automorphism formula also respects the actual sign and complement conventions. -/
theorem standard_odd_signed_complement (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (p : OctadParameters) :
    let q := (standardParameters α p).sign ((hammingNorm p.J / 2 : ℕ) : ParkerBit)
    (q1ImageConjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (rOctad (p.sign 1)).val =
        (rOctad q).val * q1ImageCenterGenerator ∧
      q1ImageConjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (rOctad p.complement).val =
        (rOctad q).val) ∧
    (representation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (vector (p.sign 1)) = -vector q ∧
      representation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (vector p.complement) = vector q) := by
  dsimp only
  rw [sign, complement, standard_odd α hα]
  simp only [ZMod.val_one, pow_one, vector_sign, vector_complement, map_neg,
    vector_standard_odd α hα, and_self]

end Sporadic.Monster.Construction.NOctad.LocalStructure.Conjugation
