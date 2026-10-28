module

public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortFamilies.Basic

/-!
# The odd short extraspecial family

The source word has the representative `f_(d + epsilon_x(d) X) - lambda_x`,
with coordinate `3` at `x` and coordinates `±1` elsewhere. It is the negative
of the ATLAS signed odd profile for the normalized Golay word. This identifies
its norm and recovers every odd minimal vector up to its antipode. The actual
triality sign formula then supplies both central lifts, proving exhaustion.
The explicit representative also determines the rank-one tensor and correction.

Source: Michael Aschbacher, *Sporadic Groups*, Lemma 27.8(3), printed p. 150
(PDF page 81, left). The lattice classification is reused from the attributed
ATLAS ports, without copying their source.
-/

@[expose] public section
noncomputable section
open Atlas.Codes Atlas.Fischer Atlas.Lattices
open scoped BigOperators
namespace Sporadic.Monster.Construction.LocalC.ShortFamilies
open TrialitySpin
attribute [local instance] Classical.propDecidable

@[simp] theorem oddCode_at (x : Omega) (d : ParkerLoop) : (oddCode x d).val x = 0 := by
  simp [oddCode, golayOne, allOnes]

theorem oddRepresentative_apply (x : Omega) (d : ParkerLoop) (i : Omega) :
    (oddRepresentative x d).val i =
      2 * golayIntegerLift (oddCode x d).val i + (if i = x then 4 else 0) - 1 := by
  change (sourceCodeVector _).val i + (sourcePointVector _).val i = _
  rw [sourceCodeVector_apply,sourcePointVector_apply]
  ring

@[simp] theorem oddRepresentative_at (x : Omega) (d : ParkerLoop) :
    (oddRepresentative x d).val x = 3 := by
  simp [oddRepresentative_apply,golayIntegerLift]

theorem oddRepresentative_profile (x : Omega) (d : ParkerLoop) :
    (oddRepresentative x d).val = -signedOddProfile {x} ∅ (oddCode x d) := by
  funext i
  rw [oddRepresentative_apply]
  by_cases hi : i = x
  · subst i
    simp [golayIntegerLift,signedOddProfile,signChange,oddProfileBase]
  · by_cases hc : (oddCode x d).val i = 0 <;>
      simp [golayIntegerLift,signedOddProfile,signChange,oddProfileBase,hi,hc]

theorem oddRepresentative_norm (x : Omega) (d : ParkerLoop) :
    integerDot (oddRepresentative x d).val (oddRepresentative x d).val = 32 := by
  rw [oddRepresentative_profile]
  have hn := signedOddProfile_norm {x} ∅ (by simp) (oddCode x d)
  simpa [integerDot] using hn

def oddShell (x : Omega) (d : ParkerLoop) : LeechShell 4 :=
  ⟨oddRepresentative x d, oddRepresentative_norm x d⟩

def rOdd (x : Omega) (d : ParkerLoop) : Lift :=
  ofRepresentative (rOddElement x d) (oddShell x d) (rOddElement_class x d)

@[simp] theorem rOdd_val (x : Omega) (d : ParkerLoop) : (rOdd x d).val = rOddElement x d := rfl

theorem rOdd_class (x : Omega) (d : ParkerLoop) :
    shortLiftClass sourceLatticeComparison (rOdd x d) = shortReduction (oddShell x d) :=
  ofRepresentative_class _ _ _

theorem rOdd_tensor (x : Omega) (d : ParkerLoop) :
    shortLiftTensor sourceLatticeComparison (rOdd x d) =
      rankOne (leechVector (oddRepresentative x d)) := ofRepresentative_tensor _ _ _

theorem rOdd_correction (x : Omega) (d : ParkerLoop) (a : NaturalSpace) :
    shortLiftCorrection sourceLatticeComparison (rOdd x d) a =
      vectorCorrection (leechVector (oddRepresentative x d)) a := ofRepresentative_correction _ _ _ _

theorem oddRepresentative_mem (x : Omega) (d : ParkerLoop) :
    (oddRepresentative x d).val ∈ oddNoFiveVectors 1 := by
  apply (odd_minimal_shell_iff _).mp
  refine ⟨(oddRepresentative x d).prop, ?_, oddRepresentative_norm x d⟩
  intro i
  rw [oddRepresentative_profile]
  have h := signedOddProfile_parity {x} ∅ (oddCode x d) i
  change (-signedOddProfile {x} ∅ (oddCode x d) i) % 2 = 1
  omega

theorem rOdd_hasShape (x : Omega) (d : ParkerLoop) :
    HasShape (oddNoFiveVectors 1) (rOdd x d) :=
  ⟨oddShell x d, (rOdd_class x d).symm, oddRepresentative_mem x d⟩

/-- The Parker-loop sign changes the actual group lift by the central involution. -/
theorem rOddElement_sign (x : Omega) (s : ParkerBit) (d : ParkerLoop) :
    rOddElement x (parkerSign s d) =
      q1ImageCenterGenerator ^ s.val * rOddElement x d := by
  simp only [rOddElement]
  rw [loopImage_sign]
  change (q1ImageCenterGenerator ^ s.val * loopImage d) *
    loopImage parkerOmega ^ (d.1.val x).val * cocodeImage (pointWord x) = _
  simp only [mul_assoc]

theorem rOdd_sign (x : Omega) (d : ParkerLoop) :
    rOdd x (parkerSign 1 d) = (shortLiftSigns sourceLatticeComparison).flip (rOdd x d) := by
  apply Subtype.ext
  change rOddElement x (parkerSign 1 d) = rOddElement x d * q1ImageCenterGenerator
  rw [rOddElement_sign]
  simpa only [show (1 : ParkerBit).val = 1 from rfl, pow_one] using
    (Subgroup.mem_center_iff.mp centerGenerator_mem (rOddElement x d)).symm

/-- Every odd minimal vector is a source representative or its antipode. -/
theorem odd_representatives (v : LeechShell 4) (hv : v.val.val ∈ oddNoFiveVectors 1) :
    ∃ x : Omega, ∃ d : ParkerLoop,
      v.val = oddRepresentative x d ∨ v.val = -oddRepresentative x d := by
  obtain ⟨⟨⟨T,hT⟩,c⟩,_,hc⟩ := Finset.mem_image.mp hv
  obtain ⟨x,rfl⟩ := Finset.card_eq_one.mp hT
  change signedOddProfile {x} ∅ c = v.val.val at hc
  refine ⟨x,(c,0),?_⟩
  rcases bit_cases (c.val x) with hx | hx
  · apply Or.inr
    apply Subtype.ext
    rw [← hc]
    have he : oddCode x (c,0) = c := by simp [oddCode,hx]
    change signedOddProfile {x} ∅ c = -(oddRepresentative x (c,0)).val
    rw [oddRepresentative_profile,he,neg_neg]
  · apply Or.inl
    apply Subtype.ext
    rw [← hc]
    funext i
    rw [oddRepresentative_apply]
    by_cases hi : i = x
    · subst i
      simp [golayIntegerLift,signedOddProfile,signChange,oddProfileBase,hx]
    · rcases bit_cases (c.val i) with hci | hci <;>
        simp [oddCode,hx,golayOne,allOnes,golayIntegerLift,signedOddProfile,signChange,
          oddProfileBase,hi,hci]

/-- Lemma 27.8(3), including both central signs in the Parker parameter. -/
theorem odd_iff (q : Lift) : HasShape (oddNoFiveVectors 1) q ↔
    ∃ x : Omega, ∃ d : ParkerLoop, rOdd x d = q := by
  constructor
  · rintro ⟨v,hv,hs⟩
    obtain ⟨x,d,hd⟩ := odd_representatives v hs
    have he : shortLiftClass sourceLatticeComparison q =
        shortLiftClass sourceLatticeComparison (rOdd x d) := by
      rw [rOdd_class,← hv]
      exact (shortReduction_eq_iff _ _).mpr hd
    rcases (shortLiftClass_eq_iff sourceLatticeComparison _ _).mp he with h | h
    · exact ⟨x,d,h.symm⟩
    · exact ⟨x,parkerSign 1 d,(rOdd_sign x d).trans h.symm⟩
  · rintro ⟨x,d,rfl⟩
    exact rOdd_hasShape x d

end Sporadic.Monster.Construction.LocalC.ShortFamilies
