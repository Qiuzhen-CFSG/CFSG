module
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Spin

/-!
# Loop calculations for the signed spin actions

Commutators and squares reduce the inverse sandwich to its sign. Standard
loop automorphisms preserve signs, inverses, and square parity; their action
on the all-ones element determines which central orbit relation they preserve.
These facts follow from `IsStandard` and the concrete Parker identities.

Source: Aschbacher, *Sporadic Groups*, Lemma 27.3(1)–(4), p. 146.
The sandwich and inverse arguments also occur in this project's
`Structure/NormalForms/Coordinates.lean`; the direct proofs here keep the
signed modules independent of the subsequent group-structure development.
-/

@[expose] public section
open Atlas.Fischer Atlas.Codes
noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin.SpinActions

private theorem multiply_twice (a d : ParkerLoop) :
    parkerLoopMultiply (parkerLoopMultiply a d) d =
      parkerSign (golayQuarterWeight d.1) a := by
  rw [parkerLoopMultiply_associator, parkerTripleIntersection_repeat, parkerSign_zero,
    parkerLoopMultiply_square]
  have hs : (0, golayQuarterWeight d.1) = parkerSign (golayQuarterWeight d.1) loopOne := by
    simp [parkerSign, loopOne]
  rw [hs, parkerLoopMultiply_sign_right, loopOne, parkerLoopMultiply_one_right]

/-- The exponent is the loop square plus its commutator with `b`, as in 27.3(2). -/
theorem inverse_sandwich (d b : ParkerLoop) :
    parkerLoopMultiply (parkerLoopMultiply (loopInverse d) b) (loopInverse d) =
      parkerSign (golayQuarterWeight d.1 + golayHalfOverlap b.1 d.1) b := by
  rw [parkerLoopMultiply_commutator (loopInverse d) b,
    parkerLoopMultiply_sign_left, multiply_twice, parkerSign_add]
  change parkerSign (golayHalfOverlap d.1 b.1 + golayQuarterWeight d.1) b = _
  rw [golayHalfOverlap_symmetric, add_comm]

theorem standard_sign (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (s : ParkerBit) (x : ParkerLoop) : e (parkerSign s x) = parkerSign s (e x) := by
  have hx : parkerSign s x = parkerLoopMultiply x (0, s) := by
    simp [parkerSign, parkerLoopMultiply, parkerMultiply]
  rw [hx, he.1, he.2.1]
  simp [parkerSign, parkerLoopMultiply, parkerMultiply]

theorem standard_inverse (e : Equiv.Perm ParkerLoop) (he : IsStandard e) (x : ParkerLoop) :
    e (loopInverse x) = loopInverse (e x) := by
  apply (loopRight (e x)).injective
  change parkerLoopMultiply (e (loopInverse x)) (e x) =
    parkerLoopMultiply (loopInverse (e x)) (e x)
  rw [← he.1, loopInverse_mul, loopInverse_mul]
  exact he.2.1 0

theorem standard_square (e : Equiv.Perm ParkerLoop) (he : IsStandard e) (x : ParkerLoop) :
    golayQuarterWeight (e x).1 = golayQuarterWeight x.1 := by
  have h := he.1 x x
  rw [parkerLoopMultiply_square, parkerLoopMultiply_square, he.2.1] at h
  exact congrArg Prod.snd h.symm

theorem standard_omega_sign (e : Equiv.Perm ParkerLoop) (he : IsStandard e) :
    e parkerOmega = parkerSign (e parkerOmega).2 parkerOmega := by
  apply Prod.ext
  · obtain ⟨g, hg⟩ := he.2.2
    exact Subtype.ext (hg parkerOmega)
  · simp [parkerSign, parkerOmega]

theorem standard_omega_odd (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (ho : e parkerOmega ≠ parkerOmega) : e parkerOmega = parkerSign 1 parkerOmega := by
  have hb : ∀ s : ParkerBit, s = 0 ∨ s = 1 := by decide
  rcases hb (e parkerOmega).2 with h | h
  · exact False.elim (ho (by rw [standard_omega_sign e he, h, parkerSign_zero]))
  · rw [standard_omega_sign e he, h]

theorem left_twist (d b : ParkerLoop) (s : ParkerBit) :
    parkerLoopMultiply d (parkerLoopMultiply b (parkerSign s parkerOmega)) =
      parkerLoopMultiply (parkerLoopMultiply d b) (parkerSign s parkerOmega) := by
  simp only [parkerLoopMultiply_sign_right, parkerOmega_associates_right]

theorem right_twist (d b : ParkerLoop) (s : ParkerBit) :
    parkerLoopMultiply (parkerLoopMultiply b (parkerSign s parkerOmega)) d =
      parkerLoopMultiply (parkerLoopMultiply b d) (parkerSign s parkerOmega) := by
  simp only [parkerLoopMultiply_sign_right, parkerLoopMultiply_sign_left]
  rw [parkerOmega_associates_middle, parkerOmega_commutes, ← parkerOmega_associates_right]

private theorem quarter_one : golayQuarterWeight golayOne = 0 := by
  have h := parkerOmega_square
  rw [parkerLoopMultiply_square] at h
  exact congrArg Prod.snd h

private theorem quarter_add_one (b : golay) :
    golayQuarterWeight (b + golayOne) = golayQuarterWeight b := by
  rw [golayQuarterWeight_add, quarter_one, golayHalfOverlap_symmetric,
    golayHalfOverlap_one, add_zero, add_zero]

theorem inverse_twist (b : ParkerLoop) (s : ParkerBit) :
    loopInverse (parkerLoopMultiply b (parkerSign s parkerOmega)) =
      parkerLoopMultiply (loopInverse b) (parkerSign s parkerOmega) := by
  rw [parkerLoopMultiply_sign_right, loopInverse_sign]
  change parkerSign s (parkerSign (golayQuarterWeight (b.1 + golayOne))
    (parkerLoopMultiply b parkerOmega)) = _
  rw [quarter_add_one, loopInverse, parkerLoopMultiply_sign_left,
    parkerLoopMultiply_sign_right, parkerSign_add, parkerSign_add, add_comm]

theorem standard_twist (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (ε : ParkerBit) (hε : e parkerOmega = parkerSign ε parkerOmega)
    (b : ParkerLoop) (s : ParkerBit) :
    e (parkerLoopMultiply b (parkerSign s parkerOmega)) =
      parkerLoopMultiply (e b) (parkerSign (s + ε) parkerOmega) := by
  rw [he.1, standard_sign e he, hε, parkerSign_add]

@[simp] theorem psi2_on_axis2 (d b : ParkerLoop) :
    psi2 d (axis2 b) = axis2
      (parkerSign (golayQuarterWeight d.1 + golayHalfOverlap b.1 d.1) b) := by
  simp only [axis2, psi2_apply, rightZero_none, leftZero_none, leftZero_some,
    rightZero_some, inverse_sandwich]

@[simp] theorem psi3_on_axis2 (d b : ParkerLoop) :
    psi3 d (axis2 b) = axis2 (parkerLoopMultiply b d) := rfl

theorem psiAut2_even_axis (e : Equiv.Perm ParkerLoop) (he : e parkerOmega = parkerOmega)
    (b : ParkerLoop) : psiAut2 e (axis2 b) = axis2 (e b) := by
  simp [psiAut2, he, diagonal, axis2]

theorem psiAut2_odd_axis (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (ho : e parkerOmega ≠ parkerOmega) (b : ParkerLoop) :
    psiAut2 e (axis2 b) = axis2 (parkerSign (golayQuarterWeight b.1) (e b)) := by
  simp only [psiAut2, if_neg ho, Equiv.trans_apply]
  change axis2 (e (loopInverse b)) = _
  rw [loopInverse, standard_sign e he]

theorem psiAut1_odd_axis (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (ho : e parkerOmega ≠ parkerOmega) (b : ParkerLoop) :
    psiAut1 e (axis2 b) = axis3 (parkerSign (golayQuarterWeight b.1) (e b)) := by
  simp only [psiAut1, if_neg ho, Equiv.trans_apply]
  change axis3 (e (loopInverse b)) = _
  rw [loopInverse, standard_sign e he]

theorem psiAut1_odd_axis3 (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (ho : e parkerOmega ≠ parkerOmega) (b : ParkerLoop) :
    psiAut1 e (axis3 b) = axis2 (parkerSign (golayQuarterWeight b.1) (e b)) := by
  simp only [psiAut1, if_neg ho, Equiv.trans_apply]
  change axis2 (e (loopInverse b)) = _
  rw [loopInverse, standard_sign e he]
end Sporadic.Monster.Construction.TrialitySpin.SpinActions
