module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.WordMatrices
import Mathlib.Tactic.FinCases

/-!
# The four base generators preserve the specified line

These are certificates for the published words in FiniteIncidence/Words.lean.
Literal binary rows and word decompositions are untrusted witnesses. Each
product is checked by kernel reduction through packedRow_spec, and all group
claims are transferred to the actual matrix subgroup. Source context:
Aschbacher–Smith, Proposition 1.3.4, printed p.511/PDF p.528; Aschbacher (1986).
See Obstructions/source/README.md for the certificate construction.
-/

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
@[expose] public section
open Subgroup
open scoped Pointwise
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound LowerBound.QuotientOrderCertificate
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.ObstructionCertificate

theorem s0_value : value (sylowGenerator 0) = wordMatrix014 := by
  change ((evaluate [(true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix014_expansion.symm

theorem s0_inverse_value :
    value ((sylowGenerator 0)⁻¹) = quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] := by
  apply inverse_value _ _ _ s0_value
  intro i
  fin_cases i <;> rfl

theorem s0_line : sylowGenerator 0 ∈ involutionMatrixLineStabilizer := by
  apply line_mem_of_inverse _ _ 23 1024 1047 s0_inverse_value
  · rfl
  · rfl
  · rfl
  · change {involutionMatrixVector 23, involutionMatrixVector 1024,
      involutionMatrixVector 1047} =
      {involutionMatrixVector 23, involutionMatrixVector 1024, involutionMatrixVector 1047}
    ext v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm, or_assoc]

theorem s1_value : value (sylowGenerator 1) = wordMatrix029 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix029_expansion.symm

theorem s1_inverse_value :
    value ((sylowGenerator 1)⁻¹) = quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] := by
  apply inverse_value _ _ _ s1_value
  intro i
  fin_cases i <;> rfl

theorem s1_line : sylowGenerator 1 ∈ involutionMatrixLineStabilizer := by
  apply line_mem_of_inverse _ _ 23 1047 1024 s1_inverse_value
  · rfl
  · rfl
  · rfl
  · change {involutionMatrixVector 23, involutionMatrixVector 1047,
      involutionMatrixVector 1024} =
      {involutionMatrixVector 23, involutionMatrixVector 1024, involutionMatrixVector 1047}
    ext v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm, or_assoc]

theorem s2_value : value (sylowGenerator 2) = wordMatrix035 := by
  change ((evaluate [(true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix035_expansion.symm

theorem s2_inverse_value :
    value ((sylowGenerator 2)⁻¹) = quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] := by
  apply inverse_value _ _ _ s2_value
  intro i
  fin_cases i <;> rfl

theorem s2_line : sylowGenerator 2 ∈ involutionMatrixLineStabilizer := by
  apply line_mem_of_inverse _ _ 23 1024 1047 s2_inverse_value
  · rfl
  · rfl
  · rfl
  · change {involutionMatrixVector 23, involutionMatrixVector 1024,
      involutionMatrixVector 1047} =
      {involutionMatrixVector 23, involutionMatrixVector 1024, involutionMatrixVector 1047}
    ext v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm, or_assoc]

theorem s3_value : value (sylowGenerator 3) = wordMatrix042 := by
  change ((evaluate [(true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix042_expansion.symm

theorem s3_inverse_value :
    value ((sylowGenerator 3)⁻¹) = quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] := by
  apply inverse_value _ _ _ s3_value
  intro i
  fin_cases i <;> rfl

theorem s3_line : sylowGenerator 3 ∈ involutionMatrixLineStabilizer := by
  apply line_mem_of_inverse _ _ 23 1047 1024 s3_inverse_value
  · rfl
  · rfl
  · rfl
  · change {involutionMatrixVector 23, involutionMatrixVector 1047,
      involutionMatrixVector 1024} =
      {involutionMatrixVector 23, involutionMatrixVector 1024, involutionMatrixVector 1047}
    ext v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm, or_assoc]


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.ObstructionCertificate
