module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.Constraints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.Small
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.Denominator

/-!
# Arithmetic interface for the remaining large-ratio exhaustion

`CaseTwoIntegerSystem` retains only proved integer consequences of the actual
characters. Its construction from the source inputs is given below, including
the complete cofactor conditions, nonzero degree divisors, all free signed
multiplicities, and the third degree, value and Suzuki equations. It does not
assert a group order or any unproved elimination. Numerical exhaustion of this
system is a separate prerequisite to the final assembly.

Two extra numerical patterns found during exploration can already be excluded
from the actual second decomposition: degrees -358 and 180 would force the
nondivisor 178 as the fifth degree, while values 7 and -2 would force an
impossible fifth value -5. These exclusions do not assert that the exploration
is exhaustive.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.14–15.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion
open LocalModelDichotomy

/-- Integer consequences of the three constituents of the third Suzuki equation. -/
public structure CaseTwoIntegerSystem (g : ℕ) (x y z a b c : ℤ) : Prop where
  cofactor : ∃ h : ℕ, 0 < h ∧ g = 40320*h ∧ ¬ 2 ∣ h ∧ ¬ 3 ∣ h
  nonzero_x : x ≠ 0
  nonzero_y : y ≠ 0
  nonzero_z : z ≠ 0
  row_x : CaseTwoRowConditions g 78 2 (x,a)
  row_y : CaseTwoRowConditions g (-329) (-7) (y,b)
  row_z : CaseTwoRowConditions g 127 1 (z,c)
  degree : 1+x-y+z = 0
  value : 1+a-b+c = 16
  suzuki : (g : ℤ) * caseTwoDenominator x y z a b c = 1118208*x*y*z

/-- The arithmetic interface inherits the three finite denominator-divisor bounds. -/
public theorem CaseTwoIntegerSystem.denominator_bounds {g : ℕ} {x y z a b c : ℤ}
    (S : CaseTwoIntegerSystem g x y z a b c) :
    let P := caseTwoDenominator x y z a b c
    P ≠ 0 ∧ P ∣ 1118208*x*(x+1) ∧ P ∣ 1118208*y*(y-1) ∧ P ∣ 1118208*z*(z+1) :=
  caseTwo_denominator_divisibility g x y z _ S.nonzero_x S.nonzero_y S.nonzero_z
    S.row_x.1 S.row_y.1 S.row_z.1 S.degree S.suzuki

noncomputable section
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

/-- Construct every integer premise from the actual second character decomposition. -/
public theorem caseTwo_integerSystem (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I)
    (hu : HasUnitMultiplicities I.induced) (F : SignedFamily G 6)
    (h1 : I.induced 0 = F.term 0 + F.term 1 + F.term 2)
    (h2 : I.induced 1 = F.term 0 + F.term 3 + F.term 4)
    (h3 : I.induced 2 = 1 + F.term 0 - F.term 3 + F.term 5) :
    CaseTwoIntegerSystem (Nat.card G)
      (caseTwoSignedDegree F 0) (caseTwoSignedDegree F 3) (caseTwoSignedDegree F 5)
      (caseTwoSignedValue I F 0) (caseTwoSignedValue I F 3) (caseTwoSignedValue I F 5) where
  cofactor := exists_order_cofactor D k L
  nonzero_x := (caseTwo_signedDegree_dvd F 0).1
  nonzero_y := (caseTwo_signedDegree_dvd F 3).1
  nonzero_z := (caseTwo_signedDegree_dvd F 5).1
  row_x := by simpa [caseTwoBase] using caseTwo_signedRow_conditions D k L I hu F h1 h2 h3 0
  row_y := by simpa [caseTwoBase] using caseTwo_signedRow_conditions D k L I hu F h1 h2 h3 3
  row_z := by simpa [caseTwoBase] using caseTwo_signedRow_conditions D k L I hu F h1 h2 h3 5
  degree := caseTwo_third_degree I F h3
  value := caseTwo_third_value I F h3
  suzuki := caseTwo_third_suzuki_int D k L I hI F h3

/-- A large ratio gives the exact integral selected-degree bound used by enumeration. -/
public theorem caseTwo_large_degree_bound {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) (F : SignedFamily G 6) (j : Fin 6)
    (hr : 1/4 < involutionRatio I (F.irreducible j)) :
    ((caseTwoSignedDegree F j).natAbs : ℤ) < 4 * (caseTwoSignedValue I F j)^2 := by
  have hd : (0 : ℚ) < (F.irreducible j).degree := by exact_mod_cast (F.irreducible j).degree_pos
  have hh := (lt_div_iff₀ hd).mp hr
  have hh' : ((F.irreducible j).degree : ℚ) < 4*(involutionValue I (F.irreducible j) : ℚ)^2 := by
    linarith
  have hi : ((F.irreducible j).degree : ℤ) < 4*(involutionValue I (F.irreducible j))^2 := by
    exact_mod_cast hh'
  rw [caseTwo_signedDegree_natAbs]
  rcases F.sign_eq j with hs | hs <;> simpa [caseTwoSignedValue, hs] using hi

/-- The second degree relation excludes the exploratory order 93824640 pattern. -/
public theorem caseTwo_exclude_degree_pattern {D : LocalData G}
    {k : TwistedModel ≃* D.centralizer} (I : SpecialInductionData D k) (F : SignedFamily G 6)
    (h1 : I.induced 0 = F.term 0 + F.term 1 + F.term 2)
    (h2 : I.induced 1 = F.term 0 + F.term 3 + F.term 4)
    (hg : Nat.card G = 93824640)
    (hx : caseTwoSignedDegree F 0 = -358) (hy : caseTwoSignedDegree F 3 = 180) : False := by
  have he := (caseTwo_first_two_degrees I F h1 h2).2
  have h4 : caseTwoSignedDegree F 4 = 178 := by omega
  have hd := (caseTwo_signedDegree_dvd F 4).2
  rw [h4, hg] at hd
  norm_num at hd

/-- The second value relation excludes the exploratory pair of values 7 and -2. -/
public theorem caseTwo_exclude_value_pattern (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hu : HasUnitMultiplicities I.induced) (F : SignedFamily G 6)
    (h1 : I.induced 0 = F.term 0 + F.term 1 + F.term 2)
    (h2 : I.induced 1 = F.term 0 + F.term 3 + F.term 4)
    (h3 : I.induced 2 = 1 + F.term 0 - F.term 3 + F.term 5)
    (ha : caseTwoSignedValue I F 0 = 7) (hb : caseTwoSignedValue I F 3 = -2) : False := by
  have he := (caseTwo_first_two_values I F h1 h2).2
  have h4 : caseTwoSignedValue I F 4 = -5 := by omega
  have hr := caseTwo_signedRow_conditions D k L I hu F h1 h2 h3 4
  obtain ⟨_, u, hu', v, hv, hval, _⟩ := hr
  change caseTwoSignedValue I F 4 = -6 + 8*u + 3*v at hval
  rw [h4] at hval
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu' hv
  rcases hu' with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;> norm_num at hval

end
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion
