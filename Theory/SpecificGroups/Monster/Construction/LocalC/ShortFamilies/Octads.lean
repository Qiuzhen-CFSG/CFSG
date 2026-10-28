module

public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortFamilies.Basic

/-!
# The octad short extraspecial family

For a Parker-loop element over an octad and an even subset `J` of that octad,
`rOctad` is the actual source word in `Q1Image`. Its explicit Leech representative
has coordinates `2 * indicator(code(c)) - 4 * indicator(J)` and norm four.
Recovery of the support and signs from the ATLAS two-four family proves
exhaustion; changing the Parker-loop sign supplies the other central lift.

The source warning is an equality in the actual group: complementing `J` within
the octad fixes `rOctad`, while negating its explicit representative. The cocode
is unchanged, and the two exponents of the involution `loopImage parkerOmega`
have equal parity. Minimal-vector reduction and the actual central sign relation
then give exact parameter criteria for equality and for opposite central signs.
The representative also gives the rank-one tensor and vector correction.

This proves the octad branch of Lemma 27.8(2), including its preceding warning.
Source: Michael Aschbacher, *Sporadic Groups*, printed p. 150 (PDF page 81,
left page). The shell classification and recovery results are reused from the
attributed ATLAS ports; no ATLAS source is copied here.
-/

@[expose] public section

open Atlas.Codes Atlas.Fischer Atlas.Lattices
open scoped BigOperators
noncomputable section
namespace Sporadic.Monster.Construction.LocalC.ShortFamilies
open TrialitySpin
attribute [local instance] Classical.propDecidable

theorem octadRepresentative_two_support (p : OctadParameters) :
    evenMagnitudeSupport (octadRepresentative p.c p.J).val 2 =
      Finset.univ.filter (fun i => p.c.1.val i ≠ 0) := by
  ext i
  simp only [evenMagnitudeSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    octadRepresentative_apply p.c p.J p.even, octadCoordinates]
  have hs := p.supported i
  by_cases hc : p.c.1.val i = 0 <;> by_cases hj : p.J i = 0 <;>
    simp_all [golayIntegerLift]

theorem octadRepresentative_mem (p : OctadParameters) :
    (octadRepresentative p.c p.J).val ∈ twoFourFamily 8 0 := by
  apply (twoFourFamily_iff _ _ _).mpr
  refine ⟨(octadRepresentative p.c p.J).prop, ?_, ?_, ?_⟩
  · intro i
    rw [octadRepresentative_apply p.c p.J p.even]
    have hs := p.supported i
    by_cases hc : p.c.1.val i = 0 <;> by_cases hj : p.J i = 0 <;>
      simp_all [octadCoordinates, golayIntegerLift]
  · rw [octadRepresentative_two_support]
    exact p.octad
  · have h : evenMagnitudeSupport (octadRepresentative p.c p.J).val 4 = ∅ := by
      ext i
      simp only [evenMagnitudeSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        octadRepresentative_apply p.c p.J p.even, octadCoordinates,
        Finset.notMem_empty, iff_false]
      have hs := p.supported i
      by_cases hc : p.c.1.val i = 0 <;> by_cases hj : p.J i = 0 <;>
        simp_all [golayIntegerLift]
    rw [h, Finset.card_empty]

theorem octadRepresentative_norm (p : OctadParameters) :
    integerDot (octadRepresentative p.c p.J).val (octadRepresentative p.c p.J).val = 32 := by
  simpa using (twoFourFamily_properties 8 0 _ (octadRepresentative_mem p)).2.2

def octadShell (p : OctadParameters) : LeechShell 4 :=
  ⟨octadRepresentative p.c p.J, octadRepresentative_norm p⟩

def rOctad (p : OctadParameters) : Lift :=
  ofRepresentative (rOctadElement p.c p.J) (octadShell p) (rOctadElement_class p.c p.J)

theorem rOctad_val (p : OctadParameters) : (rOctad p).val = rOctadElement p.c p.J := rfl

theorem rOctad_class (p : OctadParameters) :
    shortLiftClass sourceLatticeComparison (rOctad p) = shortReduction (octadShell p) :=
  ofRepresentative_class _ _ _

theorem rOctad_tensor (p : OctadParameters) :
    shortLiftTensor sourceLatticeComparison (rOctad p) =
      rankOne (leechVector (octadRepresentative p.c p.J)) :=
  ofRepresentative_tensor _ _ _

theorem rOctad_correction (p : OctadParameters) (a : NaturalSpace) :
    shortLiftCorrection sourceLatticeComparison (rOctad p) a =
      vectorCorrection (leechVector (octadRepresentative p.c p.J)) a :=
  ofRepresentative_correction _ _ _ _

def OctadParameters.sign (p : OctadParameters) (s : ParkerBit) : OctadParameters :=
  ⟨parkerSign s p.c, p.J, p.octad, p.supported, p.even⟩

theorem rOctadElement_sign (c : ParkerLoop) (J : BinaryWord) (s : ParkerBit) :
    rOctadElement (parkerSign s c) J = rOctadElement c J * q1ImageCenterGenerator ^ s.val := by
  rw [rOctadElement, loopImage_sign]
  have h := Subgroup.mem_center_iff.mp ((Subgroup.center Q1Image).pow_mem centerGenerator_mem s.val) (loopImage c)
  rw [← h, ← mul_assoc]
  rfl

theorem rOctad_sign (p : OctadParameters) :
    rOctad (p.sign 1) = (shortLiftSigns sourceLatticeComparison).flip (rOctad p) := by
  apply Subtype.ext
  exact rOctadElement_sign p.c p.J 1

theorem rOctad_hasShape (p : OctadParameters) : HasShape (twoFourFamily 8 0) (rOctad p) :=
  ⟨octadShell p, (rOctad_class p).symm, octadRepresentative_mem p⟩

theorem octad_representatives (v : LeechShell 4) (hv : v.val.val ∈ twoFourFamily 8 0) :
    ∃ p : OctadParameters, v.val = octadRepresentative p.c p.J := by
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hv
  rcases a with ⟨⟨T, hc, ht⟩, ⟨U, hd, hu⟩, ⟨s, hs⟩, t⟩
  have hU : U = ∅ := Finset.card_eq_zero.mp hu
  subst U
  let J : BinaryWord := fun i => if h : i ∈ T then s ⟨i,h⟩ else 0
  have hsum : ∑ i, J i = ∑ i : T, s i := by
    calc
      _ = ∑ i ∈ T, J i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ T)
        intro i _ hi
        simp [J, hi]
      _ = _ := by rw [← Finset.sum_attach T]; simp [J]
  let p : OctadParameters :=
    { c := (⟨supportWord T, hc⟩, 0)
      J := J
      octad := by simpa [hammingNorm, supportWord] using ht
      supported := by
        intro i hi
        by_cases h : i ∈ T
        · simp [supportWord, h]
        · simp [J, h] at hi
      even := (even_weight_iff J).mpr (hsum.trans (by simpa using hs)) }
  refine ⟨p, ?_⟩
  apply Subtype.ext
  funext i
  rw [octadRepresentative_apply p.c p.J p.even]
  rw [← ha]
  change twoFourVector T ∅ s t i = 2 * golayIntegerLift (supportWord T) i - 4 * golayIntegerLift J i
  by_cases hi : i ∈ T
  · rcases bit_cases (s ⟨i,hi⟩) with h | h <;>
      simp [twoFourVector, signedSupport, supportWord, golayIntegerLift, J, hi, h]
  · simp [twoFourVector, signedSupport, supportWord, golayIntegerLift, J, hi]

theorem octad_exhaustion (q : Lift) (hq : HasShape (twoFourFamily 8 0) q) :
    ∃ p : OctadParameters, rOctad p = q := by
  obtain ⟨v, hv, hs⟩ := hq
  obtain ⟨p, hp⟩ := octad_representatives v hs
  have h : shortLiftClass sourceLatticeComparison q = shortLiftClass sourceLatticeComparison (rOctad p) := by
    rw [rOctad_class, ← hv]
    exact (shortReduction_eq_iff _ _).mpr (Or.inl hp)
  rcases (shortLiftClass_eq_iff sourceLatticeComparison _ _).mp h with h | h
  · exact ⟨p, h.symm⟩
  · exact ⟨p.sign 1, (rOctad_sign p).trans h.symm⟩

theorem octad_hasShape_iff (q : Lift) :
    HasShape (twoFourFamily 8 0) q ↔ ∃ p : OctadParameters, rOctad p = q := by
  constructor
  · exact octad_exhaustion q
  · rintro ⟨p, rfl⟩
    exact rOctad_hasShape p

theorem octad_complement_weight (p : OctadParameters) :
    hammingNorm (p.J + p.c.1.val) + hammingNorm p.J = 8 := by
  have ho : overlap p.J p.c.1.val = hammingNorm p.J := by
    unfold overlap hammingNorm
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨And.left, fun h => ⟨h, p.supported i h⟩⟩
  have h := binary_weight_add p.J p.c.1.val
  rw [ho, p.octad] at h
  omega

def OctadParameters.complement (p : OctadParameters) : OctadParameters where
  c := p.c
  J := p.J + p.c.1.val
  octad := p.octad
  supported := by
    intro i hi hc
    have hj : p.J i = 0 := not_not.mp (mt (p.supported i) (not_not.mpr hc))
    exact hi (by simp [hc, hj])
  even := by
    have hw := octad_complement_weight p
    obtain ⟨k, hk⟩ := p.even
    exact even_iff_two_dvd.mpr (by omega)

theorem octadRepresentative_complement (p : OctadParameters) :
    octadRepresentative p.complement.c p.complement.J = -octadRepresentative p.c p.J := by
  apply Subtype.ext
  funext i
  change (octadRepresentative p.complement.c p.complement.J).val i = -(octadRepresentative p.c p.J).val i
  rw [octadRepresentative_apply _ _ p.complement.even, octadRepresentative_apply _ _ p.even]
  have hs := p.supported i
  rcases bit_cases (p.c.1.val i) with hc | hc <;> rcases bit_cases (p.J i) with hj | hj <;>
    simp_all [OctadParameters.complement, octadCoordinates, golayIntegerLift]

private theorem loopImage_omega_square : loopImage parkerOmega ^ 2 = 1 := by
  rw [Q1Image_square_coordinates]
  simp [loopImage, q1Coordinates_param, q1WordCoordinates, coordinateQuadratic,
    parkerOmega, golayQuarterWeight, golayOne, allOnes, hammingNorm]
  change q1ImageCenterGenerator ^ (6 : ParkerBit).val = 1
  have h : (6 : ParkerBit).val = 0 := by decide
  rw [h, pow_zero]

private theorem cocodeImage_add_code (J : BinaryWord) (c : golay) :
    cocodeImage (J + c.val) = cocodeImage J := by
  have hc : (Submodule.Quotient.mk c.val : Cocode) = 0 :=
    (Submodule.Quotient.mk_eq_zero golay).mpr c.prop
  simp only [cocodeImage, Submodule.Quotient.mk_add, hc, add_zero]

theorem rOctad_complement (p : OctadParameters) : rOctad p.complement = rOctad p := by
  apply Subtype.ext
  change rOctadElement p.c (p.J + p.c.1.val) = rOctadElement p.c p.J
  rw [rOctadElement, rOctadElement, cocodeImage_add_code]
  have hw := octad_complement_weight p
  obtain ⟨k, hk⟩ := p.even
  have he : (hammingNorm (p.J + p.c.1.val) / 2) % 2 = (hammingNorm p.J / 2) % 2 := by omega
  rw [pow_eq_pow_mod _ loopImage_omega_square, he, ← pow_eq_pow_mod _ loopImage_omega_square]

theorem octadRepresentative_eq_iff (p q : OctadParameters) :
    octadRepresentative p.c p.J = octadRepresentative q.c q.J ↔
      p.c.1 = q.c.1 ∧ p.J = q.J := by
  constructor
  · intro h
    have hs := congrArg (fun v : leech => evenMagnitudeSupport v.val 2) h
    rw [octadRepresentative_two_support p, octadRepresentative_two_support q] at hs
    have hc : p.c.1 = q.c.1 := by
      apply Subtype.ext
      funext i
      have hi := Finset.ext_iff.mp hs i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases bit_cases (p.c.1.val i) with hp | hp <;>
        rcases bit_cases (q.c.1.val i) with hq | hq
      · exact hp.trans hq.symm
      · exact ((hi.mpr (hq ▸ one_ne_zero)) hp).elim
      · exact ((hi.mp (hp ▸ one_ne_zero)) hq).elim
      · exact hp.trans hq.symm
    refine ⟨hc, ?_⟩
    funext i
    have hi := congrArg (fun v : leech => v.val i) h
    rw [octadRepresentative_apply _ _ p.even, octadRepresentative_apply _ _ q.even] at hi
    simp only [octadCoordinates, hc] at hi
    rcases bit_cases (p.J i) with hp | hp <;>
      rcases bit_cases (q.J i) with hq | hq <;> simp_all [golayIntegerLift]
    omega
  · rintro ⟨hc, hJ⟩
    simp only [octadRepresentative, hc, hJ]

theorem octadRepresentative_eq_neg_iff (p q : OctadParameters) :
    octadRepresentative p.c p.J = -octadRepresentative q.c q.J ↔
      p.c.1 = q.c.1 ∧ p.J = q.J + q.c.1.val := by
  rw [← octadRepresentative_complement q, octadRepresentative_eq_iff]
  rfl

theorem rOctad_class_eq_iff (p q : OctadParameters) :
    shortLiftClass sourceLatticeComparison (rOctad p) =
      shortLiftClass sourceLatticeComparison (rOctad q) ↔
    p.c.1 = q.c.1 ∧ (p.J = q.J ∨ p.J = q.J + q.c.1.val) := by
  rw [rOctad_class, rOctad_class, shortReduction_eq_iff]
  change (octadRepresentative p.c p.J = octadRepresentative q.c q.J ∨
    octadRepresentative p.c p.J = -octadRepresentative q.c q.J) ↔ _
  rw [octadRepresentative_eq_iff, octadRepresentative_eq_neg_iff, and_or_left]

private theorem loopImage_injective_of_code_eq (c d : ParkerLoop) (hc : c.1 = d.1)
    (h : loopImage c = loopImage d) : c = d := by
  have he : c = parkerSign (c.2 + d.2) d := by
    apply Prod.ext
    · exact hc
    · simp [parkerSign, add_left_comm]
  rcases bit_cases (c.2 + d.2) with hs | hs
  · simpa [hs] using he
  · rw [he, loopImage_sign, hs] at h
    change q1ImageCenterGenerator * loopImage d = loopImage d at h
    have hz : q1ImageCenterGenerator = 1 := by simpa using (mul_eq_right.mp h)
    exact (q1ImageCenterGenerator_ne_one hz).elim

private theorem rOctad_c_eq_of_J_eq (p q : OctadParameters)
    (hc : p.c.1 = q.c.1) (hJ : p.J = q.J) (h : rOctad p = rOctad q) : p.c = q.c := by
  have he := congrArg Subtype.val h
  change rOctadElement p.c p.J = rOctadElement q.c q.J at he
  unfold rOctadElement at he
  rw [hJ] at he
  exact loopImage_injective_of_code_eq p.c q.c hc (mul_left_cancel he)

theorem rOctad_eq_iff (p q : OctadParameters) :
    rOctad p = rOctad q ↔ p.c = q.c ∧ (p.J = q.J ∨ p.J = q.J + q.c.1.val) := by
  constructor
  · intro h
    obtain ⟨hc, hJ⟩ := (rOctad_class_eq_iff p q).mp (congrArg (shortLiftClass sourceLatticeComparison) h)
    refine ⟨?_, hJ⟩
    rcases hJ with hJ | hJ
    · exact rOctad_c_eq_of_J_eq p q hc hJ h
    · exact rOctad_c_eq_of_J_eq p q.complement hc hJ (h.trans (rOctad_complement q).symm)
  · rintro ⟨hc, hJ | hJ⟩
    · apply Subtype.ext
      change rOctadElement p.c p.J = rOctadElement q.c q.J
      rw [hc, hJ]
    · calc
        rOctad p = rOctad q.complement := by
          apply Subtype.ext
          change rOctadElement p.c p.J = rOctadElement q.c (q.J + q.c.1.val)
          rw [hc, hJ]
        _ = rOctad q := rOctad_complement q

theorem rOctad_eq_flip_iff (p q : OctadParameters) :
    rOctad p = (shortLiftSigns sourceLatticeComparison).flip (rOctad q) ↔
      p.c = parkerSign 1 q.c ∧ (p.J = q.J ∨ p.J = q.J + q.c.1.val) := by
  rw [← rOctad_sign, rOctad_eq_iff]
  rfl

theorem rOctadElement_complement (p : OctadParameters) :
    rOctadElement p.c (p.J + p.c.1.val) = rOctadElement p.c p.J :=
  congrArg Subtype.val (rOctad_complement p)

theorem octadRepresentative_sign (p : OctadParameters) (s : ParkerBit) :
    octadRepresentative (p.sign s).c (p.sign s).J = octadRepresentative p.c p.J := rfl

theorem rOctad_vector_sign (p : OctadParameters) :
    shortVector sourceLatticeComparison (rOctad (p.sign 1)) =
      -shortVector sourceLatticeComparison (rOctad p) := by
  rw [rOctad_sign, shortVector_sign]

end Sporadic.Monster.Construction.LocalC.ShortFamilies
