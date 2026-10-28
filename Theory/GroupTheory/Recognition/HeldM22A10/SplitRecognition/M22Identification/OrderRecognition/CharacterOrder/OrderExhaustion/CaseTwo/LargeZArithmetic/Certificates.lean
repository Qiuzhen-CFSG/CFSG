module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.LargeZArithmetic.Finite

/-!
# Kernel-checked large-Z arithmetic

For each of the 28 possible selected rows, the calculation checks every signed
divisor of the factored denominator bound and every possible quadratic root.
Each row retains all nine multiplicity choices for each of the other two rows.
The factorization identities and primality assertions are checked separately;
Python search output is not used as a premise or an oracle.

The checks are grouped by the selected value c, so each declaration checks a
bounded family within the default heartbeat budget.
The soundness application excludes every row of the actual integer system.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.14–15.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion.LargeZ

set_option maxRecDepth 10000 in
private theorem checks0 :
    rowCheck [(2, 13), (3, 2), (7, 1), (13, 1), (19, 1), (29, 1)] (-58) (-10) = true ∧
    rowCheck [(2, 13), (3, 1), (5, 1), (7, 2), (13, 1), (71, 1)] (70) (-10) = true ∧
    rowCheck [(2, 13), (3, 2), (5, 1), (7, 1), (13, 1), (31, 1), (37, 1)] (-186) (-10) = true ∧
    rowCheck [(2, 13), (3, 3), (7, 1), (11, 1), (13, 1), (199, 1)] (198) (-10) = true ∧
    rowCheck [(2, 13), (3, 1), (7, 1), (13, 1), (157, 1), (313, 1)] (-314) (-10) = true ∧
    rowCheck [(2, 13), (3, 2), (7, 1), (13, 1), (109, 1), (163, 1)] (326) (-10) = true := by
  and_intros <;> decide +kernel

set_option maxRecDepth 10000 in
private theorem checks1 :
    rowCheck [(2, 13), (3, 1), (5, 2), (7, 1), (13, 2)] (25) (-7) = true ∧
    rowCheck [(2, 13), (3, 2), (7, 1), (13, 1), (17, 1), (103, 1)] (-103) (-7) = true ∧
    rowCheck [(2, 13), (3, 3), (7, 2), (11, 1), (13, 1), (17, 1)] (153) (-7) = true := by
  and_intros <;> decide +kernel

set_option maxRecDepth 10000 in
private theorem checks2 :
    rowCheck [(2, 14), (3, 1), (5, 1), (7, 1), (13, 1), (19, 1)] (-20) (-4) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checks3 :
    rowCheck [(2, 13), (3, 1), (7, 1), (13, 1)] (1) (1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checks4 :
    rowCheck [(2, 14), (3, 1), (7, 1), (11, 1), (13, 1), (43, 1)] (-44) (4) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checks5 :
    rowCheck [(2, 13), (3, 1), (7, 1), (11, 1), (13, 1), (23, 1)] (22) (6) = true ∧
    rowCheck [(2, 13), (3, 2), (5, 1), (7, 2), (13, 1), (53, 1)] (-106) (6) = true := by
  and_intros <;> decide +kernel

set_option maxRecDepth 10000 in
private theorem checks6 :
    rowCheck [(2, 13), (3, 1), (7, 1), (11, 1), (13, 1), (23, 1)] (-23) (9) = true ∧
    rowCheck [(2, 13), (3, 2), (5, 1), (7, 2), (13, 1), (53, 1)] (105) (9) = true ∧
    rowCheck [(2, 13), (3, 2), (5, 2), (7, 1), (13, 1), (151, 1)] (-151) (9) = true ∧
    rowCheck [(2, 13), (3, 3), (7, 1), (13, 2), (233, 1)] (233) (9) = true ∧
    rowCheck [(2, 13), (3, 3), (7, 1), (13, 1), (31, 1), (139, 1)] (-279) (9) = true := by
  and_intros <;> decide +kernel

set_option maxRecDepth 10000 in
private theorem checks7 :
    rowCheck [(2, 14), (3, 2), (5, 1), (7, 1), (13, 1), (61, 1)] (60) (12) = true ∧
    rowCheck [(2, 14), (3, 1), (7, 1), (13, 1), (17, 1), (67, 1)] (-68) (12) = true ∧
    rowCheck [(2, 14), (3, 4), (7, 2), (13, 1), (47, 1)] (188) (12) = true ∧
    rowCheck [(2, 14), (3, 2), (5, 1), (7, 3), (13, 2)] (-196) (12) = true ∧
    rowCheck [(2, 14), (3, 1), (7, 1), (13, 1), (79, 1), (317, 1)] (316) (12) = true ∧
    rowCheck [(2, 14), (3, 5), (7, 1), (13, 1), (17, 1), (19, 1)] (-324) (12) = true ∧
    rowCheck [(2, 14), (3, 2), (5, 1), (7, 1), (13, 1), (37, 1), (89, 1)] (444) (12) = true ∧
    rowCheck [(2, 14), (3, 1), (7, 1), (11, 1), (13, 1), (41, 1), (113, 1)] (-452) (12) = true ∧
    rowCheck [(2, 14), (3, 2), (7, 1), (11, 1), (13, 2), (191, 1)] (572) (12) = true := by
  and_intros <;> decide +kernel

/-- Every possible selected row contradicts the integer system. -/
public theorem rows_impossible {g : ℕ} {x y z a b c : ℤ}
    (S : CaseTwoIntegerSystem g x y z a b c) (hz : (z,c) ∈ zRows) : False := by
  obtain ⟨h00, h01, h02, h03, h04, h05⟩ := checks0
  obtain ⟨h06, h07, h08⟩ := checks1
  have h09 := checks2
  have h10 := checks3
  have h11 := checks4
  obtain ⟨h12, h13⟩ := checks5
  obtain ⟨h14, h15, h16, h17, h18⟩ := checks6
  obtain ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := checks7
  simp only [zRows, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hz
  rcases hz with
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  · exact rowCheck_sound S (fs := [(2, 13), (3, 2), (7, 1), (13, 1), (19, 1), (29, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h00
  · exact rowCheck_sound S (fs := [(2, 13), (3, 1), (5, 1), (7, 2), (13, 1), (71, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h01
  · exact rowCheck_sound S (fs := [(2, 13), (3, 2), (5, 1), (7, 1), (13, 1), (31, 1), (37, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h02
  · exact rowCheck_sound S (fs := [(2, 13), (3, 3), (7, 1), (11, 1), (13, 1), (199, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h03
  · exact rowCheck_sound S (fs := [(2, 13), (3, 1), (7, 1), (13, 1), (157, 1), (313, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h04
  · exact rowCheck_sound S (fs := [(2, 13), (3, 2), (7, 1), (13, 1), (109, 1), (163, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h05
  · exact rowCheck_sound S (fs := [(2, 13), (3, 1), (5, 2), (7, 1), (13, 2)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h06
  · exact rowCheck_sound S (fs := [(2, 13), (3, 2), (7, 1), (13, 1), (17, 1), (103, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h07
  · exact rowCheck_sound S (fs := [(2, 13), (3, 3), (7, 2), (11, 1), (13, 1), (17, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h08
  · exact rowCheck_sound S (fs := [(2, 14), (3, 1), (5, 1), (7, 1), (13, 1), (19, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h09
  · exact rowCheck_sound S (fs := [(2, 13), (3, 1), (7, 1), (13, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h10
  · exact rowCheck_sound S (fs := [(2, 14), (3, 1), (7, 1), (11, 1), (13, 1), (43, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h11
  · exact rowCheck_sound S (fs := [(2, 13), (3, 1), (7, 1), (11, 1), (13, 1), (23, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h12
  · exact rowCheck_sound S (fs := [(2, 13), (3, 2), (5, 1), (7, 2), (13, 1), (53, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h13
  · exact rowCheck_sound S (fs := [(2, 13), (3, 1), (7, 1), (11, 1), (13, 1), (23, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h14
  · exact rowCheck_sound S (fs := [(2, 13), (3, 2), (5, 1), (7, 2), (13, 1), (53, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h15
  · exact rowCheck_sound S (fs := [(2, 13), (3, 2), (5, 2), (7, 1), (13, 1), (151, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h16
  · exact rowCheck_sound S (fs := [(2, 13), (3, 3), (7, 1), (13, 2), (233, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h17
  · exact rowCheck_sound S (fs := [(2, 13), (3, 3), (7, 1), (13, 1), (31, 1), (139, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h18
  · exact rowCheck_sound S (fs := [(2, 14), (3, 2), (5, 1), (7, 1), (13, 1), (61, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h19
  · exact rowCheck_sound S (fs := [(2, 14), (3, 1), (7, 1), (13, 1), (17, 1), (67, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h20
  · exact rowCheck_sound S (fs := [(2, 14), (3, 4), (7, 2), (13, 1), (47, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h21
  · exact rowCheck_sound S (fs := [(2, 14), (3, 2), (5, 1), (7, 3), (13, 2)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h22
  · exact rowCheck_sound S (fs := [(2, 14), (3, 1), (7, 1), (13, 1), (79, 1), (317, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h23
  · exact rowCheck_sound S (fs := [(2, 14), (3, 5), (7, 1), (13, 1), (17, 1), (19, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h24
  · exact rowCheck_sound S (fs := [(2, 14), (3, 2), (5, 1), (7, 1), (13, 1), (37, 1), (89, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h25
  · exact rowCheck_sound S (fs := [(2, 14), (3, 1), (7, 1), (11, 1), (13, 1), (41, 1), (113, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h26
  · exact rowCheck_sound S (fs := [(2, 14), (3, 2), (7, 1), (11, 1), (13, 2), (191, 1)])
      (by norm_num) (by norm_num [factorsValue]) (by norm_num) h27

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion.LargeZ
