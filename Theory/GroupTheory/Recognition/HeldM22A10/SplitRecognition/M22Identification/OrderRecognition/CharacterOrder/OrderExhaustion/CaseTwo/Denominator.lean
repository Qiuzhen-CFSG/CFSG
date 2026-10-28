module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.Constraints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.Rows

/-!
# Divisibility of the cleared third Suzuki denominator

Write `x,y,z` for the signed degrees at indices 0,3,5 and `a,b,c` for their
signed involution values. The third Suzuki identity is `g P = 1118208 x y z`.
Since each actual degree divides g, cancellation gives that P divides each
of `1118208xy`, `1118208xz`, and `1118208yz`. The degree-zero relation then
makes P a divisor of `1118208x(x+1)`, `1118208y(y-1)`, and `1118208z(z+1)`.
A bound on any selected degree thus restricts the possible denominator.

Source: the degree divisibility and Suzuki equations in Z. Janko,
*A characterization of the Mathieu simple groups, I*, J. Algebra 9 (1968),
Section 7, pp.14–15. The cancellation argument is supplied here explicitly.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion
open LocalModelDichotomy

/-- The integer obtained by clearing the three signed degrees. -/
@[expose] public def caseTwoDenominator (x y z a b c : ℤ) : ℤ :=
  x*y*z + a^2*y*z - b^2*x*z + c^2*x*y

private theorem denominator_dvd_of_cancel {g P u R : ℤ} (hu : u ≠ 0)
    (hd : u ∣ g) (he : g*P = R*u) : P ∣ R := by
  apply (mul_dvd_mul_iff_right hu).mp
  rw [← he]
  simpa only [mul_comm] using mul_dvd_mul_left P hd

/-- The three divisor bounds follow from degree divisibility and the degree-zero relation. -/
public theorem caseTwo_denominator_divisibility (g x y z P : ℤ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hxd : x ∣ g) (hyd : y ∣ g) (hzd : z ∣ g)
    (hdegree : 1 + x - y + z = 0) (he : g*P = 1118208*x*y*z) :
    P ≠ 0 ∧ P ∣ 1118208*x*(x+1) ∧ P ∣ 1118208*y*(y-1) ∧ P ∣ 1118208*z*(z+1) := by
  have hP : P ≠ 0 := by
    intro h
    rw [h, mul_zero] at he
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hx) hy) hz) he.symm
  have hxy : P ∣ 1118208*x*y := denominator_dvd_of_cancel hz hzd he
  have hxz : P ∣ 1118208*x*z := denominator_dvd_of_cancel hy hyd (he.trans (by ring))
  have hyz : P ∣ 1118208*y*z := denominator_dvd_of_cancel hx hxd (he.trans (by ring))
  refine ⟨hP, ?_, ?_, ?_⟩
  · have hd := dvd_sub hxy hxz
    have hdg : y-z = x+1 := by omega
    rwa [← mul_sub, hdg] at hd
  · convert dvd_add hxy hyz using 1 <;> first | rfl | skip
    calc
      1118208*y*(y-1) = 1118208*y*(x+z) := by congr 1; omega
      _ = 1118208*x*y + 1118208*y*z := by ring
  · convert dvd_sub hyz hxz using 1 <;> first | rfl | skip
    calc
      1118208*z*(z+1) = 1118208*z*(y-x) := by congr 1; omega
      _ = 1118208*y*z - 1118208*x*z := by ring

noncomputable section
variable {G : Type*} [Group G] [Finite G]

/-- Apply the denominator bounds to the actual characters of the second decomposition. -/
public theorem caseTwo_denominator_constraints (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I) (F : SignedFamily G 6)
    (h3 : I.induced 2 = 1 + F.term 0 - F.term 3 + F.term 5) :
    let x := caseTwoSignedDegree F 0
    let y := caseTwoSignedDegree F 3
    let z := caseTwoSignedDegree F 5
    let P := caseTwoDenominator x y z
      (caseTwoSignedValue I F 0) (caseTwoSignedValue I F 3) (caseTwoSignedValue I F 5)
    P ≠ 0 ∧ P ∣ 1118208*x*(x+1) ∧ P ∣ 1118208*y*(y-1) ∧ P ∣ 1118208*z*(z+1) := by
  dsimp only
  exact caseTwo_denominator_divisibility (Nat.card G) _ _ _ _
    (caseTwo_signedDegree_dvd F 0).1 (caseTwo_signedDegree_dvd F 3).1
    (caseTwo_signedDegree_dvd F 5).1 (caseTwo_signedDegree_dvd F 0).2
    (caseTwo_signedDegree_dvd F 3).2 (caseTwo_signedDegree_dvd F 5).2
    (caseTwo_third_degree I F h3) (caseTwo_third_suzuki_int D k L I hI F h3)

end
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion
