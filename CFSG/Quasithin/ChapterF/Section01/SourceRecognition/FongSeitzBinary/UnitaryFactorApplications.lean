module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFactorComparisons
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.BinaryUnitaryLocal

/-!
# Chapter 12 unitary local comparisons and the binary action branch

Apply the nonperfect factor-cover comparisons to the same chosen-module
source pair, preserving its full Borel and both endpoint markings. At q ≥ 4
the proved unitary (2B) theorem discharges the second endpoint containment;
the original linear quotient discharges the first. The SU₃ comparison
retains the exact scalar projection to the faithful PSU₃ local group.

The complete regularity sieve now has an alternative consisting of the
actual solvable degree-nine local action and its normal PSU₃(2) subgroup of
order 72. This is not a type-VI exclusion. The finite marked quotient and
split data remain earlier-source inputs, and exhaustive seven-row selection,
minimality and final marked amalgam assembly remain open.
Source: DGS Theorem D, p.224; Fong--Seitz I (2A)--(2B), (5B)--(5C);
AS F.1.1--3 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- Both source kernels, or the actual degree-nine action with its normal PSU3(2) subgroup. -/
theorem rankOne_global_regularity_or_binary_unitary_action
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    (∀ i : Fin 2, simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (MarkedLocal.endpointMap Q e i) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) i)) ∨
    (Group.IsSolvable (localGroup Q split 1) ∧ Nat.card (Panel Q 1) = 9 ∧
      ∃ A : Subgroup (localGroup Q split 1), A.Normal ∧ Nat.card A = 72 ∧
        ClassicalGroup.IsPSU A 3 2) := by
  let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  obtain ⟨T₁,hT₁⟩ := hf.sylow 1
  rcases MarkedLocal.remainder_le_kernel_or_binary_unitary_action Q e hf split 1 T₁ hT₁ with h1 | hs
  · refine Or.inl ?_
    intro i
    fin_cases i
    · have h0 := MarkedLocal.linear_remainder_le_kernel_of_model Q e hf split 0 hpsl
      exact ⟨h0,MarkedLocal.remainder_comap_of_containment Q e split 0 h0⟩
    · exact h1
  · exact Or.inr hs

/-- The literal SU3 endpoint comparison discharges (2B) for q ≥ 4 without perfectness. -/
theorem rankOne_global_specialUnitary_factor_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits)
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {m : ℕ} (hm : 2 ≤ m) (hc : Nat.card E = (2^m)^2)
    (hconj : ∀ x, J.conj x = x^(2^m))
    (ν : (R ⧸ pCore 2 R) ≃* J.specialSubgroup) :
    let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
    letI := MarkedLocal.originalRadicalInClosure_normal Q e hf split 1
    (∀ i : Fin 2, simpleRemainder Q split i ≤ localKernel Q i) ∧
    ∃ a : MarkedLocal.originalRankOne Q e split 1 ≃* J.specialSubgroup,
      ∃ b : localGroup Q split 1 ≃* ProjectiveSpecialUnitaryMatrixGroup J,
        ∃ c : (MarkedLocal.originalLocalClosure Q e split 1 ⧸
          MarkedLocal.originalRadicalInClosure Q e split 1) ≃* J.specialSubgroup,
          (∀ r, J.specialToProjective (a r) = b (MarkedLocal.originalRootProjection Q e split 1 r)) ∧
          (∀ r, c (QuotientGroup.mk' _ (inclusion
            (MarkedLocal.originalRankOne_le_localClosure Q e split 1) r)) = a r) ∧
          (∀ l : R, c (QuotientGroup.mk' _ (MarkedLocal.originalFactorIntoClosure Q e hf split 1 l)) =
            ν (QuotientGroup.mk' (pCore 2 R) l)) ∧
          (RootLocalCover.projection Q split 1).ker = center (rankOne Q split 1) := by
  let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  let := MarkedLocal.originalRadicalInClosure_normal Q e hf split 1
  obtain ⟨T₁,hT₁⟩ := hf.sylow 1
  have h1 := MarkedLocal.specialUnitary_remainder_le_kernel Q e hf split 1 T₁ hT₁ J hm hc hconj ν
  refine ⟨?_,MarkedLocal.specialUnitary_factor_comparison Q e hf split 1 T₁ hT₁ J
    (by omega) hc hconj h1 ν⟩
  intro i
  fin_cases i
  · exact MarkedLocal.linear_remainder_le_kernel_of_model Q e hf split 0 hpsl
  · exact h1

/-- The literal projective endpoint comparison discharges (2B) for q ≥ 4 without perfectness. -/
theorem rankOne_global_projectiveUnitary_factor_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits)
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {m : ℕ} (hm : 2 ≤ m) (hc : Nat.card E = (2^m)^2)
    (hconj : ∀ x, J.conj x = x^(2^m))
    (μ : (R ⧸ pCore 2 R) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
    letI := MarkedLocal.originalRadicalInClosure_normal Q e hf split 1
    (∀ i : Fin 2, simpleRemainder Q split i ≤ localKernel Q i) ∧
    ∃ a : MarkedLocal.originalRankOne Q e split 1 ≃* ProjectiveSpecialUnitaryMatrixGroup J,
      ∃ b : localGroup Q split 1 ≃* ProjectiveSpecialUnitaryMatrixGroup J,
        ∃ c : (MarkedLocal.originalLocalClosure Q e split 1 ⧸
          MarkedLocal.originalRadicalInClosure Q e split 1) ≃* ProjectiveSpecialUnitaryMatrixGroup J,
          (∀ r, a r = b (MarkedLocal.originalRootProjection Q e split 1 r)) ∧
          (∀ r, c (QuotientGroup.mk' _ (inclusion
            (MarkedLocal.originalRankOne_le_localClosure Q e split 1) r)) = a r) ∧
          (∀ l : R, c (QuotientGroup.mk' _ (MarkedLocal.originalFactorIntoClosure Q e hf split 1 l)) =
            μ (QuotientGroup.mk' (pCore 2 R) l)) := by
  let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  let := MarkedLocal.originalRadicalInClosure_normal Q e hf split 1
  obtain ⟨T₁,hT₁⟩ := hf.sylow 1
  have h1 := MarkedLocal.projectiveUnitary_remainder_le_kernel Q e hf split 1 T₁ hT₁ J hm hc hconj μ
  refine ⟨?_,MarkedLocal.projectiveUnitary_factor_comparison Q e hf split 1 T₁ hT₁ J
    (by omega) hc hconj h1 μ⟩
  intro i
  fin_cases i
  · exact MarkedLocal.linear_remainder_le_kernel_of_model Q e hf split 0 hpsl
  · exact h1

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
