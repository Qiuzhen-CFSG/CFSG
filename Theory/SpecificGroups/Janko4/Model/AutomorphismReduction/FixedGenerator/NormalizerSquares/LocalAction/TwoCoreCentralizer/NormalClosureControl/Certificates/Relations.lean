module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.Generators
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.Certificates.Products00
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.Certificates.Products01
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.Certificates.Products02
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.Certificates.Products03
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.Certificates.Products04
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.Certificates.Products05
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.Certificates.Products06
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.Certificates.Products07
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.Certificates.Products08
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.Certificates.Products09
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.Certificates.Products10
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.Certificates.Products11
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.Certificates.Products12
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.Certificates.Products13
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.Certificates.Products14
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.Certificates.Products15
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.Certificates.Products16
import Mathlib.Tactic.FinCases

/-!
# Relations of the max2 normal-closure generators

Packed products certify all pairwise commutators modulo the distinguished
central involution and the action of the two local generators. The faithful
representation from `Generators` transfers every relation to the relative
local subgroup. Source and witness provenance are in `Certificates.Rows`.
-/

@[expose] public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl
open Janko4.GeneratorCertificates Certificates

set_option maxRecDepth 10000

private lemma decoded_product {a b c : Vector ℕ 112} (hc : packedMul a b = c) :
    decodeRows a * decodeRows b = decodeRows c := by rw [← decode_packedMul, hc]

private lemma decoded_common {a b c d z : Vector ℕ 112}
    (ha : packedMul a b = z) (hb : packedMul c d = z) :
    decodeRows a * decodeRows b = decodeRows c * decodeRows d := by
  rw [decoded_product ha, decoded_product hb]

private lemma eval_conj {G M : Type*} [Group G] [Monoid M] (f : G →* M)
    {a g : G} {A B C : M} (ha : f a = A) (hg : f g = B)
    (hc : A * B = B * C) : f (g⁻¹ * a * g) = C := by
  calc
    f (g⁻¹ * a * g) = f g⁻¹ * (A * B) := by rw [map_mul, map_mul, ha, hg, mul_assoc]
    _ = f g⁻¹ * (B * C) := by rw [hc]
    _ = C := by rw [← hg, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

private lemma eval_involution_e0 : representation subgroupInvolution = decodeRows e0Rows :=
  representation_involution

lemma eval_basis0 : representation (basis 0) = decodeRows e0Rows := representation_involution
lemma eval_basis1 : representation (basis 1) = decodeRows e1Rows := representation_seed

lemma eval_basis2 : representation (basis 2) = decodeRows e2Rows :=
  eval_conj representation eval_basis1 representation_y
    (decoded_common product_word2left product_word2right)

lemma eval_basis3 : representation (basis 3) = decodeRows e3Rows :=
  eval_conj representation eval_basis2 representation_y
    (decoded_common product_word3left product_word3right)

lemma eval_basis4 : representation (basis 4) = decodeRows e4Rows :=
  eval_conj representation eval_basis3 representation_x
    (decoded_common product_word4left product_word4right)

lemma eval_basis5 : representation (basis 5) = decodeRows e5Rows :=
  eval_conj representation eval_basis4 representation_y
    (decoded_common product_word5left product_word5right)

lemma eval_basis6 : representation (basis 6) = decodeRows e6Rows :=
  eval_conj representation eval_basis5 representation_x
    (decoded_common product_word6left product_word6right)

lemma eval_basis7 : representation (basis 7) = decodeRows e7Rows :=
  eval_conj representation eval_basis5 representation_y
    (decoded_common product_word7left product_word7right)

lemma eval_basis8 : representation (basis 8) = decodeRows e8Rows :=
  eval_conj representation eval_basis6 representation_y
    (decoded_common product_word8left product_word8right)

lemma eval_basis9 : representation (basis 9) = decodeRows e9Rows :=
  eval_conj representation eval_basis7 representation_x
    (decoded_common product_word9left product_word9right)

lemma eval_basis10 : representation (basis 10) = decodeRows e10Rows :=
  eval_conj representation eval_basis8 representation_x
    (decoded_common product_word10left product_word10right)

lemma eval_basis11 : representation (basis 11) = decodeRows e11Rows :=
  eval_conj representation eval_basis8 representation_y
    (decoded_common product_word11left product_word11right)

lemma eval_basis12 : representation (basis 12) = decodeRows e12Rows :=
  eval_conj representation eval_basis9 representation_y
    (decoded_common product_word12left product_word12right)

lemma representation_basis (i : Fin 13) : representation (basis i) = decodeRows (basisRows i) := by
  fin_cases i
  · exact eval_basis0
  · exact eval_basis1
  · exact eval_basis2
  · exact eval_basis3
  · exact eval_basis4
  · exact eval_basis5
  · exact eval_basis6
  · exact eval_basis7
  · exact eval_basis8
  · exact eval_basis9
  · exact eval_basis10
  · exact eval_basis11
  · exact eval_basis12

lemma relation_1_2 : basis 1 * basis 2 = basis 2 * basis 1 := by
  apply representation_injective
  simp only [map_mul, eval_basis1, eval_basis2]
  exact decoded_common product_comm1_2left product_comm1_2right

lemma relation_1_3 : basis 1 * basis 3 = basis 3 * basis 1 := by
  apply representation_injective
  simp only [map_mul, eval_basis1, eval_basis3]
  exact decoded_common product_comm1_3left product_comm1_3right

lemma relation_1_4 : basis 1 * basis 4 = basis 4 * basis 1 := by
  apply representation_injective
  simp only [map_mul, eval_basis1, eval_basis4]
  exact decoded_common product_comm1_4left product_comm1_4right

lemma relation_1_5 : basis 1 * basis 5 = basis 5 * basis 1 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis1, eval_basis5, eval_involution_e0]
  rw [decoded_product product_comm1_5left,
    decoded_product product_comm1_5reverse, decoded_product product_comm1_5right]

lemma relation_1_6 : basis 1 * basis 6 = basis 6 * basis 1 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis1, eval_basis6, eval_involution_e0]
  rw [decoded_product product_comm1_6left,
    decoded_product product_comm1_6reverse, decoded_product product_comm1_6right]

lemma relation_1_7 : basis 1 * basis 7 = basis 7 * basis 1 := by
  apply representation_injective
  simp only [map_mul, eval_basis1, eval_basis7]
  exact decoded_common product_comm1_7left product_comm1_7right

lemma relation_1_8 : basis 1 * basis 8 = basis 8 * basis 1 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis1, eval_basis8, eval_involution_e0]
  rw [decoded_product product_comm1_8left,
    decoded_product product_comm1_8reverse, decoded_product product_comm1_8right]

lemma relation_1_9 : basis 1 * basis 9 = basis 9 * basis 1 := by
  apply representation_injective
  simp only [map_mul, eval_basis1, eval_basis9]
  exact decoded_common product_comm1_9left product_comm1_9right

lemma relation_1_10 : basis 1 * basis 10 = basis 10 * basis 1 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis1, eval_basis10, eval_involution_e0]
  rw [decoded_product product_comm1_10left,
    decoded_product product_comm1_10reverse, decoded_product product_comm1_10right]

lemma relation_1_11 : basis 1 * basis 11 = basis 11 * basis 1 := by
  apply representation_injective
  simp only [map_mul, eval_basis1, eval_basis11]
  exact decoded_common product_comm1_11left product_comm1_11right

lemma relation_1_12 : basis 1 * basis 12 = basis 12 * basis 1 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis1, eval_basis12, eval_involution_e0]
  rw [decoded_product product_comm1_12left,
    decoded_product product_comm1_12reverse, decoded_product product_comm1_12right]

lemma relation_2_3 : basis 2 * basis 3 = basis 3 * basis 2 := by
  apply representation_injective
  simp only [map_mul, eval_basis2, eval_basis3]
  exact decoded_common product_comm2_3left product_comm2_3right

lemma relation_2_4 : basis 2 * basis 4 = basis 4 * basis 2 := by
  apply representation_injective
  simp only [map_mul, eval_basis2, eval_basis4]
  exact decoded_common product_comm2_4left product_comm2_4right

lemma relation_2_5 : basis 2 * basis 5 = basis 5 * basis 2 := by
  apply representation_injective
  simp only [map_mul, eval_basis2, eval_basis5]
  exact decoded_common product_comm2_5left product_comm2_5right

lemma relation_2_6 : basis 2 * basis 6 = basis 6 * basis 2 := by
  apply representation_injective
  simp only [map_mul, eval_basis2, eval_basis6]
  exact decoded_common product_comm2_6left product_comm2_6right

lemma relation_2_7 : basis 2 * basis 7 = basis 7 * basis 2 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis2, eval_basis7, eval_involution_e0]
  rw [decoded_product product_comm2_7left,
    decoded_product product_comm2_7reverse, decoded_product product_comm2_7right]

lemma relation_2_8 : basis 2 * basis 8 = basis 8 * basis 2 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis2, eval_basis8, eval_involution_e0]
  rw [decoded_product product_comm2_8left,
    decoded_product product_comm2_8reverse, decoded_product product_comm2_8right]

lemma relation_2_9 : basis 2 * basis 9 = basis 9 * basis 2 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis2, eval_basis9, eval_involution_e0]
  rw [decoded_product product_comm2_9left,
    decoded_product product_comm2_9reverse, decoded_product product_comm2_9right]

lemma relation_2_10 : basis 2 * basis 10 = basis 10 * basis 2 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis2, eval_basis10, eval_involution_e0]
  rw [decoded_product product_comm2_10left,
    decoded_product product_comm2_10reverse, decoded_product product_comm2_10right]

lemma relation_2_11 : basis 2 * basis 11 = basis 11 * basis 2 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis2, eval_basis11, eval_involution_e0]
  rw [decoded_product product_comm2_11left,
    decoded_product product_comm2_11reverse, decoded_product product_comm2_11right]

lemma relation_2_12 : basis 2 * basis 12 = basis 12 * basis 2 := by
  apply representation_injective
  simp only [map_mul, eval_basis2, eval_basis12]
  exact decoded_common product_comm2_12left product_comm2_12right

lemma relation_3_4 : basis 3 * basis 4 = basis 4 * basis 3 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis3, eval_basis4, eval_involution_e0]
  rw [decoded_product product_comm3_4left,
    decoded_product product_comm3_4reverse, decoded_product product_comm3_4right]

lemma relation_3_5 : basis 3 * basis 5 = basis 5 * basis 3 := by
  apply representation_injective
  simp only [map_mul, eval_basis3, eval_basis5]
  exact decoded_common product_comm3_5left product_comm3_5right

lemma relation_3_6 : basis 3 * basis 6 = basis 6 * basis 3 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis3, eval_basis6, eval_involution_e0]
  rw [decoded_product product_comm3_6left,
    decoded_product product_comm3_6reverse, decoded_product product_comm3_6right]

lemma relation_3_7 : basis 3 * basis 7 = basis 7 * basis 3 := by
  apply representation_injective
  simp only [map_mul, eval_basis3, eval_basis7]
  exact decoded_common product_comm3_7left product_comm3_7right

lemma relation_3_8 : basis 3 * basis 8 = basis 8 * basis 3 := by
  apply representation_injective
  simp only [map_mul, eval_basis3, eval_basis8]
  exact decoded_common product_comm3_8left product_comm3_8right

lemma relation_3_9 : basis 3 * basis 9 = basis 9 * basis 3 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis3, eval_basis9, eval_involution_e0]
  rw [decoded_product product_comm3_9left,
    decoded_product product_comm3_9reverse, decoded_product product_comm3_9right]

lemma relation_3_10 : basis 3 * basis 10 = basis 10 * basis 3 := by
  apply representation_injective
  simp only [map_mul, eval_basis3, eval_basis10]
  exact decoded_common product_comm3_10left product_comm3_10right

lemma relation_3_11 : basis 3 * basis 11 = basis 11 * basis 3 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis3, eval_basis11, eval_involution_e0]
  rw [decoded_product product_comm3_11left,
    decoded_product product_comm3_11reverse, decoded_product product_comm3_11right]

lemma relation_3_12 : basis 3 * basis 12 = basis 12 * basis 3 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis3, eval_basis12, eval_involution_e0]
  rw [decoded_product product_comm3_12left,
    decoded_product product_comm3_12reverse, decoded_product product_comm3_12right]

lemma relation_4_5 : basis 4 * basis 5 = basis 5 * basis 4 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis4, eval_basis5, eval_involution_e0]
  rw [decoded_product product_comm4_5left,
    decoded_product product_comm4_5reverse, decoded_product product_comm4_5right]

lemma relation_4_6 : basis 4 * basis 6 = basis 6 * basis 4 := by
  apply representation_injective
  simp only [map_mul, eval_basis4, eval_basis6]
  exact decoded_common product_comm4_6left product_comm4_6right

lemma relation_4_7 : basis 4 * basis 7 = basis 7 * basis 4 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis4, eval_basis7, eval_involution_e0]
  rw [decoded_product product_comm4_7left,
    decoded_product product_comm4_7reverse, decoded_product product_comm4_7right]

lemma relation_4_8 : basis 4 * basis 8 = basis 8 * basis 4 := by
  apply representation_injective
  simp only [map_mul, eval_basis4, eval_basis8]
  exact decoded_common product_comm4_8left product_comm4_8right

lemma relation_4_9 : basis 4 * basis 9 = basis 9 * basis 4 := by
  apply representation_injective
  simp only [map_mul, eval_basis4, eval_basis9]
  exact decoded_common product_comm4_9left product_comm4_9right

lemma relation_4_10 : basis 4 * basis 10 = basis 10 * basis 4 := by
  apply representation_injective
  simp only [map_mul, eval_basis4, eval_basis10]
  exact decoded_common product_comm4_10left product_comm4_10right

lemma relation_4_11 : basis 4 * basis 11 = basis 11 * basis 4 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis4, eval_basis11, eval_involution_e0]
  rw [decoded_product product_comm4_11left,
    decoded_product product_comm4_11reverse, decoded_product product_comm4_11right]

lemma relation_4_12 : basis 4 * basis 12 = basis 12 * basis 4 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis4, eval_basis12, eval_involution_e0]
  rw [decoded_product product_comm4_12left,
    decoded_product product_comm4_12reverse, decoded_product product_comm4_12right]

lemma relation_5_6 : basis 5 * basis 6 = basis 6 * basis 5 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis5, eval_basis6, eval_involution_e0]
  rw [decoded_product product_comm5_6left,
    decoded_product product_comm5_6reverse, decoded_product product_comm5_6right]

lemma relation_5_7 : basis 5 * basis 7 = basis 7 * basis 5 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis5, eval_basis7, eval_involution_e0]
  rw [decoded_product product_comm5_7left,
    decoded_product product_comm5_7reverse, decoded_product product_comm5_7right]

lemma relation_5_8 : basis 5 * basis 8 = basis 8 * basis 5 := by
  apply representation_injective
  simp only [map_mul, eval_basis5, eval_basis8]
  exact decoded_common product_comm5_8left product_comm5_8right

lemma relation_5_9 : basis 5 * basis 9 = basis 9 * basis 5 := by
  apply representation_injective
  simp only [map_mul, eval_basis5, eval_basis9]
  exact decoded_common product_comm5_9left product_comm5_9right

lemma relation_5_10 : basis 5 * basis 10 = basis 10 * basis 5 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis5, eval_basis10, eval_involution_e0]
  rw [decoded_product product_comm5_10left,
    decoded_product product_comm5_10reverse, decoded_product product_comm5_10right]

lemma relation_5_11 : basis 5 * basis 11 = basis 11 * basis 5 := by
  apply representation_injective
  simp only [map_mul, eval_basis5, eval_basis11]
  exact decoded_common product_comm5_11left product_comm5_11right

lemma relation_5_12 : basis 5 * basis 12 = basis 12 * basis 5 := by
  apply representation_injective
  simp only [map_mul, eval_basis5, eval_basis12]
  exact decoded_common product_comm5_12left product_comm5_12right

lemma relation_6_7 : basis 6 * basis 7 = basis 7 * basis 6 := by
  apply representation_injective
  simp only [map_mul, eval_basis6, eval_basis7]
  exact decoded_common product_comm6_7left product_comm6_7right

lemma relation_6_8 : basis 6 * basis 8 = basis 8 * basis 6 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis6, eval_basis8, eval_involution_e0]
  rw [decoded_product product_comm6_8left,
    decoded_product product_comm6_8reverse, decoded_product product_comm6_8right]

lemma relation_6_9 : basis 6 * basis 9 = basis 9 * basis 6 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis6, eval_basis9, eval_involution_e0]
  rw [decoded_product product_comm6_9left,
    decoded_product product_comm6_9reverse, decoded_product product_comm6_9right]

lemma relation_6_10 : basis 6 * basis 10 = basis 10 * basis 6 := by
  apply representation_injective
  simp only [map_mul, eval_basis6, eval_basis10]
  exact decoded_common product_comm6_10left product_comm6_10right

lemma relation_6_11 : basis 6 * basis 11 = basis 11 * basis 6 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis6, eval_basis11, eval_involution_e0]
  rw [decoded_product product_comm6_11left,
    decoded_product product_comm6_11reverse, decoded_product product_comm6_11right]

lemma relation_6_12 : basis 6 * basis 12 = basis 12 * basis 6 := by
  apply representation_injective
  simp only [map_mul, eval_basis6, eval_basis12]
  exact decoded_common product_comm6_12left product_comm6_12right

lemma relation_7_8 : basis 7 * basis 8 = basis 8 * basis 7 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis7, eval_basis8, eval_involution_e0]
  rw [decoded_product product_comm7_8left,
    decoded_product product_comm7_8reverse, decoded_product product_comm7_8right]

lemma relation_7_9 : basis 7 * basis 9 = basis 9 * basis 7 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis7, eval_basis9, eval_involution_e0]
  rw [decoded_product product_comm7_9left,
    decoded_product product_comm7_9reverse, decoded_product product_comm7_9right]

lemma relation_7_10 : basis 7 * basis 10 = basis 10 * basis 7 := by
  apply representation_injective
  simp only [map_mul, eval_basis7, eval_basis10]
  exact decoded_common product_comm7_10left product_comm7_10right

lemma relation_7_11 : basis 7 * basis 11 = basis 11 * basis 7 := by
  apply representation_injective
  simp only [map_mul, eval_basis7, eval_basis11]
  exact decoded_common product_comm7_11left product_comm7_11right

lemma relation_7_12 : basis 7 * basis 12 = basis 12 * basis 7 := by
  apply representation_injective
  simp only [map_mul, eval_basis7, eval_basis12]
  exact decoded_common product_comm7_12left product_comm7_12right

lemma relation_8_9 : basis 8 * basis 9 = basis 9 * basis 8 := by
  apply representation_injective
  simp only [map_mul, eval_basis8, eval_basis9]
  exact decoded_common product_comm8_9left product_comm8_9right

lemma relation_8_10 : basis 8 * basis 10 = basis 10 * basis 8 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis8, eval_basis10, eval_involution_e0]
  rw [decoded_product product_comm8_10left,
    decoded_product product_comm8_10reverse, decoded_product product_comm8_10right]

lemma relation_8_11 : basis 8 * basis 11 = basis 11 * basis 8 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis8, eval_basis11, eval_involution_e0]
  rw [decoded_product product_comm8_11left,
    decoded_product product_comm8_11reverse, decoded_product product_comm8_11right]

lemma relation_8_12 : basis 8 * basis 12 = basis 12 * basis 8 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis8, eval_basis12, eval_involution_e0]
  rw [decoded_product product_comm8_12left,
    decoded_product product_comm8_12reverse, decoded_product product_comm8_12right]

lemma relation_9_10 : basis 9 * basis 10 = basis 10 * basis 9 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis9, eval_basis10, eval_involution_e0]
  rw [decoded_product product_comm9_10left,
    decoded_product product_comm9_10reverse, decoded_product product_comm9_10right]

lemma relation_9_11 : basis 9 * basis 11 = basis 11 * basis 9 := by
  apply representation_injective
  simp only [map_mul, eval_basis9, eval_basis11]
  exact decoded_common product_comm9_11left product_comm9_11right

lemma relation_9_12 : basis 9 * basis 12 = basis 12 * basis 9 := by
  apply representation_injective
  simp only [map_mul, eval_basis9, eval_basis12]
  exact decoded_common product_comm9_12left product_comm9_12right

lemma relation_10_11 : basis 10 * basis 11 = basis 11 * basis 10 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis10, eval_basis11, eval_involution_e0]
  rw [decoded_product product_comm10_11left,
    decoded_product product_comm10_11reverse, decoded_product product_comm10_11right]

lemma relation_10_12 : basis 10 * basis 12 = basis 12 * basis 10 * subgroupInvolution := by
  apply representation_injective
  simp only [map_mul, eval_basis10, eval_basis12, eval_involution_e0]
  rw [decoded_product product_comm10_12left,
    decoded_product product_comm10_12reverse, decoded_product product_comm10_12right]

lemma relation_11_12 : basis 11 * basis 12 = basis 12 * basis 11 := by
  apply representation_injective
  simp only [map_mul, eval_basis11, eval_basis12]
  exact decoded_common product_comm11_12left product_comm11_12right

private lemma relation_symm {G : Type*} [Group G] {a b t : G}
    (ht : t ^ 2 = 1) (hc : a * b = b * a ∨ a * b = b * a * t) :
    b * a = a * b ∨ b * a = a * b * t := by
  rcases hc with hc | hc
  · exact Or.inl hc.symm
  · apply Or.inr
    rw [hc, mul_assoc (b * a), ← pow_two, ht, mul_one]

private lemma basis_commutator_row0 (j : Fin 13) :
    basis 0 * basis j = basis j * basis 0 ∨
      basis 0 * basis j = basis j * basis 0 * subgroupInvolution := by
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 1)).symm
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 2)).symm
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 3)).symm
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 4)).symm
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 5)).symm
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 6)).symm
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 7)).symm
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 8)).symm
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 9)).symm
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 10)).symm
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 11)).symm
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 12)).symm

private lemma basis_commutator_row1 (j : Fin 13) :
    basis 1 * basis j = basis j * basis 1 ∨
      basis 1 * basis j = basis j * basis 1 * subgroupInvolution := by
  fin_cases j
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 1))
  · exact Or.inl rfl
  · exact Or.inl relation_1_2
  · exact Or.inl relation_1_3
  · exact Or.inl relation_1_4
  · exact Or.inr relation_1_5
  · exact Or.inr relation_1_6
  · exact Or.inl relation_1_7
  · exact Or.inr relation_1_8
  · exact Or.inl relation_1_9
  · exact Or.inr relation_1_10
  · exact Or.inl relation_1_11
  · exact Or.inr relation_1_12

private lemma basis_commutator_row2 (j : Fin 13) :
    basis 2 * basis j = basis j * basis 2 ∨
      basis 2 * basis j = basis j * basis 2 * subgroupInvolution := by
  fin_cases j
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 2))
  · exact relation_symm (a := basis 1) (b := basis 2) involution_pow_two (Or.inl relation_1_2)
  · exact Or.inl rfl
  · exact Or.inl relation_2_3
  · exact Or.inl relation_2_4
  · exact Or.inl relation_2_5
  · exact Or.inl relation_2_6
  · exact Or.inr relation_2_7
  · exact Or.inr relation_2_8
  · exact Or.inr relation_2_9
  · exact Or.inr relation_2_10
  · exact Or.inr relation_2_11
  · exact Or.inl relation_2_12

private lemma basis_commutator_row3 (j : Fin 13) :
    basis 3 * basis j = basis j * basis 3 ∨
      basis 3 * basis j = basis j * basis 3 * subgroupInvolution := by
  fin_cases j
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 3))
  · exact relation_symm (a := basis 1) (b := basis 3) involution_pow_two (Or.inl relation_1_3)
  · exact relation_symm (a := basis 2) (b := basis 3) involution_pow_two (Or.inl relation_2_3)
  · exact Or.inl rfl
  · exact Or.inr relation_3_4
  · exact Or.inl relation_3_5
  · exact Or.inr relation_3_6
  · exact Or.inl relation_3_7
  · exact Or.inl relation_3_8
  · exact Or.inr relation_3_9
  · exact Or.inl relation_3_10
  · exact Or.inr relation_3_11
  · exact Or.inr relation_3_12

private lemma basis_commutator_row4 (j : Fin 13) :
    basis 4 * basis j = basis j * basis 4 ∨
      basis 4 * basis j = basis j * basis 4 * subgroupInvolution := by
  fin_cases j
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 4))
  · exact relation_symm (a := basis 1) (b := basis 4) involution_pow_two (Or.inl relation_1_4)
  · exact relation_symm (a := basis 2) (b := basis 4) involution_pow_two (Or.inl relation_2_4)
  · exact relation_symm (a := basis 3) (b := basis 4) involution_pow_two (Or.inr relation_3_4)
  · exact Or.inl rfl
  · exact Or.inr relation_4_5
  · exact Or.inl relation_4_6
  · exact Or.inr relation_4_7
  · exact Or.inl relation_4_8
  · exact Or.inl relation_4_9
  · exact Or.inl relation_4_10
  · exact Or.inr relation_4_11
  · exact Or.inr relation_4_12

private lemma basis_commutator_row5 (j : Fin 13) :
    basis 5 * basis j = basis j * basis 5 ∨
      basis 5 * basis j = basis j * basis 5 * subgroupInvolution := by
  fin_cases j
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 5))
  · exact relation_symm (a := basis 1) (b := basis 5) involution_pow_two (Or.inr relation_1_5)
  · exact relation_symm (a := basis 2) (b := basis 5) involution_pow_two (Or.inl relation_2_5)
  · exact relation_symm (a := basis 3) (b := basis 5) involution_pow_two (Or.inl relation_3_5)
  · exact relation_symm (a := basis 4) (b := basis 5) involution_pow_two (Or.inr relation_4_5)
  · exact Or.inl rfl
  · exact Or.inr relation_5_6
  · exact Or.inr relation_5_7
  · exact Or.inl relation_5_8
  · exact Or.inl relation_5_9
  · exact Or.inr relation_5_10
  · exact Or.inl relation_5_11
  · exact Or.inl relation_5_12

private lemma basis_commutator_row6 (j : Fin 13) :
    basis 6 * basis j = basis j * basis 6 ∨
      basis 6 * basis j = basis j * basis 6 * subgroupInvolution := by
  fin_cases j
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 6))
  · exact relation_symm (a := basis 1) (b := basis 6) involution_pow_two (Or.inr relation_1_6)
  · exact relation_symm (a := basis 2) (b := basis 6) involution_pow_two (Or.inl relation_2_6)
  · exact relation_symm (a := basis 3) (b := basis 6) involution_pow_two (Or.inr relation_3_6)
  · exact relation_symm (a := basis 4) (b := basis 6) involution_pow_two (Or.inl relation_4_6)
  · exact relation_symm (a := basis 5) (b := basis 6) involution_pow_two (Or.inr relation_5_6)
  · exact Or.inl rfl
  · exact Or.inl relation_6_7
  · exact Or.inr relation_6_8
  · exact Or.inr relation_6_9
  · exact Or.inl relation_6_10
  · exact Or.inr relation_6_11
  · exact Or.inl relation_6_12

private lemma basis_commutator_row7 (j : Fin 13) :
    basis 7 * basis j = basis j * basis 7 ∨
      basis 7 * basis j = basis j * basis 7 * subgroupInvolution := by
  fin_cases j
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 7))
  · exact relation_symm (a := basis 1) (b := basis 7) involution_pow_two (Or.inl relation_1_7)
  · exact relation_symm (a := basis 2) (b := basis 7) involution_pow_two (Or.inr relation_2_7)
  · exact relation_symm (a := basis 3) (b := basis 7) involution_pow_two (Or.inl relation_3_7)
  · exact relation_symm (a := basis 4) (b := basis 7) involution_pow_two (Or.inr relation_4_7)
  · exact relation_symm (a := basis 5) (b := basis 7) involution_pow_two (Or.inr relation_5_7)
  · exact relation_symm (a := basis 6) (b := basis 7) involution_pow_two (Or.inl relation_6_7)
  · exact Or.inl rfl
  · exact Or.inr relation_7_8
  · exact Or.inr relation_7_9
  · exact Or.inl relation_7_10
  · exact Or.inl relation_7_11
  · exact Or.inl relation_7_12

private lemma basis_commutator_row8 (j : Fin 13) :
    basis 8 * basis j = basis j * basis 8 ∨
      basis 8 * basis j = basis j * basis 8 * subgroupInvolution := by
  fin_cases j
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 8))
  · exact relation_symm (a := basis 1) (b := basis 8) involution_pow_two (Or.inr relation_1_8)
  · exact relation_symm (a := basis 2) (b := basis 8) involution_pow_two (Or.inr relation_2_8)
  · exact relation_symm (a := basis 3) (b := basis 8) involution_pow_two (Or.inl relation_3_8)
  · exact relation_symm (a := basis 4) (b := basis 8) involution_pow_two (Or.inl relation_4_8)
  · exact relation_symm (a := basis 5) (b := basis 8) involution_pow_two (Or.inl relation_5_8)
  · exact relation_symm (a := basis 6) (b := basis 8) involution_pow_two (Or.inr relation_6_8)
  · exact relation_symm (a := basis 7) (b := basis 8) involution_pow_two (Or.inr relation_7_8)
  · exact Or.inl rfl
  · exact Or.inl relation_8_9
  · exact Or.inr relation_8_10
  · exact Or.inr relation_8_11
  · exact Or.inr relation_8_12

private lemma basis_commutator_row9 (j : Fin 13) :
    basis 9 * basis j = basis j * basis 9 ∨
      basis 9 * basis j = basis j * basis 9 * subgroupInvolution := by
  fin_cases j
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 9))
  · exact relation_symm (a := basis 1) (b := basis 9) involution_pow_two (Or.inl relation_1_9)
  · exact relation_symm (a := basis 2) (b := basis 9) involution_pow_two (Or.inr relation_2_9)
  · exact relation_symm (a := basis 3) (b := basis 9) involution_pow_two (Or.inr relation_3_9)
  · exact relation_symm (a := basis 4) (b := basis 9) involution_pow_two (Or.inl relation_4_9)
  · exact relation_symm (a := basis 5) (b := basis 9) involution_pow_two (Or.inl relation_5_9)
  · exact relation_symm (a := basis 6) (b := basis 9) involution_pow_two (Or.inr relation_6_9)
  · exact relation_symm (a := basis 7) (b := basis 9) involution_pow_two (Or.inr relation_7_9)
  · exact relation_symm (a := basis 8) (b := basis 9) involution_pow_two (Or.inl relation_8_9)
  · exact Or.inl rfl
  · exact Or.inr relation_9_10
  · exact Or.inl relation_9_11
  · exact Or.inl relation_9_12

private lemma basis_commutator_row10 (j : Fin 13) :
    basis 10 * basis j = basis j * basis 10 ∨
      basis 10 * basis j = basis j * basis 10 * subgroupInvolution := by
  fin_cases j
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 10))
  · exact relation_symm (a := basis 1) (b := basis 10) involution_pow_two (Or.inr relation_1_10)
  · exact relation_symm (a := basis 2) (b := basis 10) involution_pow_two (Or.inr relation_2_10)
  · exact relation_symm (a := basis 3) (b := basis 10) involution_pow_two (Or.inl relation_3_10)
  · exact relation_symm (a := basis 4) (b := basis 10) involution_pow_two (Or.inl relation_4_10)
  · exact relation_symm (a := basis 5) (b := basis 10) involution_pow_two (Or.inr relation_5_10)
  · exact relation_symm (a := basis 6) (b := basis 10) involution_pow_two (Or.inl relation_6_10)
  · exact relation_symm (a := basis 7) (b := basis 10) involution_pow_two (Or.inl relation_7_10)
  · exact relation_symm (a := basis 8) (b := basis 10) involution_pow_two (Or.inr relation_8_10)
  · exact relation_symm (a := basis 9) (b := basis 10) involution_pow_two (Or.inr relation_9_10)
  · exact Or.inl rfl
  · exact Or.inr relation_10_11
  · exact Or.inr relation_10_12

private lemma basis_commutator_row11 (j : Fin 13) :
    basis 11 * basis j = basis j * basis 11 ∨
      basis 11 * basis j = basis j * basis 11 * subgroupInvolution := by
  fin_cases j
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 11))
  · exact relation_symm (a := basis 1) (b := basis 11) involution_pow_two (Or.inl relation_1_11)
  · exact relation_symm (a := basis 2) (b := basis 11) involution_pow_two (Or.inr relation_2_11)
  · exact relation_symm (a := basis 3) (b := basis 11) involution_pow_two (Or.inr relation_3_11)
  · exact relation_symm (a := basis 4) (b := basis 11) involution_pow_two (Or.inr relation_4_11)
  · exact relation_symm (a := basis 5) (b := basis 11) involution_pow_two (Or.inl relation_5_11)
  · exact relation_symm (a := basis 6) (b := basis 11) involution_pow_two (Or.inr relation_6_11)
  · exact relation_symm (a := basis 7) (b := basis 11) involution_pow_two (Or.inl relation_7_11)
  · exact relation_symm (a := basis 8) (b := basis 11) involution_pow_two (Or.inr relation_8_11)
  · exact relation_symm (a := basis 9) (b := basis 11) involution_pow_two (Or.inl relation_9_11)
  · exact relation_symm (a := basis 10) (b := basis 11) involution_pow_two (Or.inr relation_10_11)
  · exact Or.inl rfl
  · exact Or.inl relation_11_12

private lemma basis_commutator_row12 (j : Fin 13) :
    basis 12 * basis j = basis j * basis 12 ∨
      basis 12 * basis j = basis j * basis 12 * subgroupInvolution := by
  fin_cases j
  · exact Or.inl ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 12))
  · exact relation_symm (a := basis 1) (b := basis 12) involution_pow_two (Or.inr relation_1_12)
  · exact relation_symm (a := basis 2) (b := basis 12) involution_pow_two (Or.inl relation_2_12)
  · exact relation_symm (a := basis 3) (b := basis 12) involution_pow_two (Or.inr relation_3_12)
  · exact relation_symm (a := basis 4) (b := basis 12) involution_pow_two (Or.inr relation_4_12)
  · exact relation_symm (a := basis 5) (b := basis 12) involution_pow_two (Or.inl relation_5_12)
  · exact relation_symm (a := basis 6) (b := basis 12) involution_pow_two (Or.inl relation_6_12)
  · exact relation_symm (a := basis 7) (b := basis 12) involution_pow_two (Or.inl relation_7_12)
  · exact relation_symm (a := basis 8) (b := basis 12) involution_pow_two (Or.inr relation_8_12)
  · exact relation_symm (a := basis 9) (b := basis 12) involution_pow_two (Or.inl relation_9_12)
  · exact relation_symm (a := basis 10) (b := basis 12) involution_pow_two (Or.inr relation_10_12)
  · exact relation_symm (a := basis 11) (b := basis 12) involution_pow_two (Or.inl relation_11_12)
  · exact Or.inl rfl

lemma basis_commutator (i j : Fin 13) :
    basis i * basis j = basis j * basis i ∨
      basis i * basis j = basis j * basis i * subgroupInvolution := by
  fin_cases i
  · exact basis_commutator_row0 j
  · exact basis_commutator_row1 j
  · exact basis_commutator_row2 j
  · exact basis_commutator_row3 j
  · exact basis_commutator_row4 j
  · exact basis_commutator_row5 j
  · exact basis_commutator_row6 j
  · exact basis_commutator_row7 j
  · exact basis_commutator_row8 j
  · exact basis_commutator_row9 j
  · exact basis_commutator_row10 j
  · exact basis_commutator_row11 j
  · exact basis_commutator_row12 j

/-- Increasing binary product of the thirteen fixed generators. -/
def maskProduct {M : Type*} [Monoid M] (e : Fin 13 → M) (m : ℕ) : M :=
  (List.ofFn (fun i => if m.testBit i.val then e i else 1)).prod

lemma map_maskProduct {G M : Type*} [Monoid G] [Monoid M] (f : G →* M)
    (e : Fin 13 → G) (m : ℕ) :
    f (maskProduct e m) = maskProduct (fun i => f (e i)) m := by
  simp only [maskProduct, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  split_ifs with h <;> simp [h]

lemma maskProduct_mem {G : Type*} [Group G] (K : Subgroup G)
    (e : Fin 13 → G) (he : ∀ i, e i ∈ K) (m : ℕ) : maskProduct e m ∈ K := by
  apply K.list_prod_mem
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  split_ifs
  · exact he i
  · exact K.one_mem

lemma expand_mask1 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 1 = e 0 := by
  have hm (j : Fin 13) : (1 : ℕ).testBit j.val = ![true, false, false, false, false, false, false, false, false, false, false, false, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask1 : maskProduct (fun i => decodeRows (basisRows i)) 1 =
    decodeRows e0Rows := by
  exact expand_mask1 (fun i => decodeRows (basisRows i))

lemma expand_mask2 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 2 = e 1 := by
  have hm (j : Fin 13) : (2 : ℕ).testBit j.val = ![false, true, false, false, false, false, false, false, false, false, false, false, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask2 : maskProduct (fun i => decodeRows (basisRows i)) 2 =
    decodeRows e1Rows := by
  exact expand_mask2 (fun i => decodeRows (basisRows i))

lemma expand_mask3 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 3 = e 0 * (e 1) := by
  have hm (j : Fin 13) : (3 : ℕ).testBit j.val = ![true, true, false, false, false, false, false, false, false, false, false, false, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask3 : maskProduct (fun i => decodeRows (basisRows i)) 3 =
    decodeRows mask3_0Rows := by
  rw [← decoded_product product_mask3_0]
  exact expand_mask3 (fun i => decodeRows (basisRows i))

lemma expand_mask4 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 4 = e 2 := by
  have hm (j : Fin 13) : (4 : ℕ).testBit j.val = ![false, false, true, false, false, false, false, false, false, false, false, false, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask4 : maskProduct (fun i => decodeRows (basisRows i)) 4 =
    decodeRows e2Rows := by
  exact expand_mask4 (fun i => decodeRows (basisRows i))

lemma expand_mask5 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 5 = e 0 * (e 2) := by
  have hm (j : Fin 13) : (5 : ℕ).testBit j.val = ![true, false, true, false, false, false, false, false, false, false, false, false, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask5 : maskProduct (fun i => decodeRows (basisRows i)) 5 =
    decodeRows mask5_0Rows := by
  rw [← decoded_product product_mask5_0]
  exact expand_mask5 (fun i => decodeRows (basisRows i))

lemma expand_mask8 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 8 = e 3 := by
  have hm (j : Fin 13) : (8 : ℕ).testBit j.val = ![false, false, false, true, false, false, false, false, false, false, false, false, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask8 : maskProduct (fun i => decodeRows (basisRows i)) 8 =
    decodeRows e3Rows := by
  exact expand_mask8 (fun i => decodeRows (basisRows i))

lemma expand_mask16 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 16 = e 4 := by
  have hm (j : Fin 13) : (16 : ℕ).testBit j.val = ![false, false, false, false, true, false, false, false, false, false, false, false, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask16 : maskProduct (fun i => decodeRows (basisRows i)) 16 =
    decodeRows e4Rows := by
  exact expand_mask16 (fun i => decodeRows (basisRows i))

lemma expand_mask32 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 32 = e 5 := by
  have hm (j : Fin 13) : (32 : ℕ).testBit j.val = ![false, false, false, false, false, true, false, false, false, false, false, false, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask32 : maskProduct (fun i => decodeRows (basisRows i)) 32 =
    decodeRows e5Rows := by
  exact expand_mask32 (fun i => decodeRows (basisRows i))

lemma expand_mask64 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 64 = e 6 := by
  have hm (j : Fin 13) : (64 : ℕ).testBit j.val = ![false, false, false, false, false, false, true, false, false, false, false, false, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask64 : maskProduct (fun i => decodeRows (basisRows i)) 64 =
    decodeRows e6Rows := by
  exact expand_mask64 (fun i => decodeRows (basisRows i))

lemma expand_mask128 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 128 = e 7 := by
  have hm (j : Fin 13) : (128 : ℕ).testBit j.val = ![false, false, false, false, false, false, false, true, false, false, false, false, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask128 : maskProduct (fun i => decodeRows (basisRows i)) 128 =
    decodeRows e7Rows := by
  exact expand_mask128 (fun i => decodeRows (basisRows i))

lemma expand_mask256 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 256 = e 8 := by
  have hm (j : Fin 13) : (256 : ℕ).testBit j.val = ![false, false, false, false, false, false, false, false, true, false, false, false, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask256 : maskProduct (fun i => decodeRows (basisRows i)) 256 =
    decodeRows e8Rows := by
  exact expand_mask256 (fun i => decodeRows (basisRows i))

lemma expand_mask512 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 512 = e 9 := by
  have hm (j : Fin 13) : (512 : ℕ).testBit j.val = ![false, false, false, false, false, false, false, false, false, true, false, false, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask512 : maskProduct (fun i => decodeRows (basisRows i)) 512 =
    decodeRows e9Rows := by
  exact expand_mask512 (fun i => decodeRows (basisRows i))

lemma expand_mask1024 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 1024 = e 10 := by
  have hm (j : Fin 13) : (1024 : ℕ).testBit j.val = ![false, false, false, false, false, false, false, false, false, false, true, false, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask1024 : maskProduct (fun i => decodeRows (basisRows i)) 1024 =
    decodeRows e10Rows := by
  exact expand_mask1024 (fun i => decodeRows (basisRows i))

lemma expand_mask2048 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 2048 = e 11 := by
  have hm (j : Fin 13) : (2048 : ℕ).testBit j.val = ![false, false, false, false, false, false, false, false, false, false, false, true, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask2048 : maskProduct (fun i => decodeRows (basisRows i)) 2048 =
    decodeRows e11Rows := by
  exact expand_mask2048 (fun i => decodeRows (basisRows i))

lemma expand_mask2171 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 2171 = e 0 * (e 1 * (e 3 * (e 4 * (e 5 * (e 6 * (e 11)))))) := by
  have hm (j : Fin 13) : (2171 : ℕ).testBit j.val = ![true, true, false, true, true, true, true, false, false, false, false, true, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask2171 : maskProduct (fun i => decodeRows (basisRows i)) 2171 =
    decodeRows mask2171_0Rows := by
  rw [← decoded_product product_mask2171_0, ← decoded_product product_mask2171_1, ← decoded_product product_mask2171_3, ← decoded_product product_mask2171_4, ← decoded_product product_mask2171_5, ← decoded_product product_mask2171_6]
  exact expand_mask2171 (fun i => decodeRows (basisRows i))

lemma expand_mask4096 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 4096 = e 12 := by
  have hm (j : Fin 13) : (4096 : ℕ).testBit j.val = ![false, false, false, false, false, false, false, false, false, false, false, false, true] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask4096 : maskProduct (fun i => decodeRows (basisRows i)) 4096 =
    decodeRows e12Rows := by
  exact expand_mask4096 (fun i => decodeRows (basisRows i))

lemma expand_mask5964 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 5964 = e 2 * (e 3 * (e 6 * (e 8 * (e 9 * (e 10 * (e 12)))))) := by
  have hm (j : Fin 13) : (5964 : ℕ).testBit j.val = ![false, false, true, true, false, false, true, false, true, true, true, false, true] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask5964 : maskProduct (fun i => decodeRows (basisRows i)) 5964 =
    decodeRows mask5964_2Rows := by
  rw [← decoded_product product_mask5964_2, ← decoded_product product_mask5964_3, ← decoded_product product_mask5964_6, ← decoded_product product_mask5964_8, ← decoded_product product_mask5964_9, ← decoded_product product_mask5964_10]
  exact expand_mask5964 (fun i => decodeRows (basisRows i))

lemma expand_mask6046 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 6046 = e 1 * (e 2 * (e 3 * (e 4 * (e 7 * (e 8 * (e 9 * (e 10 * (e 12)))))))) := by
  have hm (j : Fin 13) : (6046 : ℕ).testBit j.val = ![false, true, true, true, true, false, false, true, true, true, true, false, true] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask6046 : maskProduct (fun i => decodeRows (basisRows i)) 6046 =
    decodeRows mask6046_1Rows := by
  rw [← decoded_product product_mask6046_1, ← decoded_product product_mask6046_2, ← decoded_product product_mask6046_3, ← decoded_product product_mask6046_4, ← decoded_product product_mask6046_7, ← decoded_product product_mask6046_8, ← decoded_product product_mask6046_9, ← decoded_product product_mask6046_10]
  exact expand_mask6046 (fun i => decodeRows (basisRows i))

lemma expand_mask7428 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 7428 = e 2 * (e 8 * (e 10 * (e 11 * (e 12)))) := by
  have hm (j : Fin 13) : (7428 : ℕ).testBit j.val = ![false, false, true, false, false, false, false, false, true, false, true, true, true] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask7428 : maskProduct (fun i => decodeRows (basisRows i)) 7428 =
    decodeRows mask7428_2Rows := by
  rw [← decoded_product product_mask7428_2, ← decoded_product product_mask7428_8, ← decoded_product product_mask7428_10, ← decoded_product product_mask7428_11]
  exact expand_mask7428 (fun i => decodeRows (basisRows i))

lemma action_x0 : subgroupX⁻¹ * basis 0 * subgroupX =
    maskProduct basis 1 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask1]
  exact eval_conj representation eval_basis0 representation_x
    (decoded_common product_actionx0left product_actionx0right)

lemma action_x1 : subgroupX⁻¹ * basis 1 * subgroupX =
    maskProduct basis 3 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask3]
  exact eval_conj representation eval_basis1 representation_x
    (decoded_common product_actionx1left product_actionx1right)

lemma action_x2 : subgroupX⁻¹ * basis 2 * subgroupX =
    maskProduct basis 5 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask5]
  exact eval_conj representation eval_basis2 representation_x
    (decoded_common product_actionx2left product_actionx2right)

lemma action_x3 : subgroupX⁻¹ * basis 3 * subgroupX =
    maskProduct basis 16 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask16]
  exact eval_conj representation eval_basis3 representation_x
    (decoded_common product_actionx3left product_actionx3right)

lemma action_x4 : subgroupX⁻¹ * basis 4 * subgroupX =
    maskProduct basis 8 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask8]
  exact eval_conj representation eval_basis4 representation_x
    (decoded_common product_actionx4left product_actionx4right)

lemma action_x5 : subgroupX⁻¹ * basis 5 * subgroupX =
    maskProduct basis 64 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask64]
  exact eval_conj representation eval_basis5 representation_x
    (decoded_common product_actionx5left product_actionx5right)

lemma action_x6 : subgroupX⁻¹ * basis 6 * subgroupX =
    maskProduct basis 32 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask32]
  exact eval_conj representation eval_basis6 representation_x
    (decoded_common product_actionx6left product_actionx6right)

lemma action_x7 : subgroupX⁻¹ * basis 7 * subgroupX =
    maskProduct basis 512 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask512]
  exact eval_conj representation eval_basis7 representation_x
    (decoded_common product_actionx7left product_actionx7right)

lemma action_x8 : subgroupX⁻¹ * basis 8 * subgroupX =
    maskProduct basis 1024 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask1024]
  exact eval_conj representation eval_basis8 representation_x
    (decoded_common product_actionx8left product_actionx8right)

lemma action_x9 : subgroupX⁻¹ * basis 9 * subgroupX =
    maskProduct basis 128 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask128]
  exact eval_conj representation eval_basis9 representation_x
    (decoded_common product_actionx9left product_actionx9right)

lemma action_x10 : subgroupX⁻¹ * basis 10 * subgroupX =
    maskProduct basis 256 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask256]
  exact eval_conj representation eval_basis10 representation_x
    (decoded_common product_actionx10left product_actionx10right)

lemma action_x11 : subgroupX⁻¹ * basis 11 * subgroupX =
    maskProduct basis 2171 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask2171]
  exact eval_conj representation eval_basis11 representation_x
    (decoded_common product_actionx11left product_actionx11right)

lemma action_x12 : subgroupX⁻¹ * basis 12 * subgroupX =
    maskProduct basis 6046 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask6046]
  exact eval_conj representation eval_basis12 representation_x
    (decoded_common product_actionx12left product_actionx12right)

lemma basis_action_x (i : Fin 13) : subgroupX⁻¹ * basis i * subgroupX =
    maskProduct basis (xMasks i) := by
  fin_cases i
  · exact action_x0
  · exact action_x1
  · exact action_x2
  · exact action_x3
  · exact action_x4
  · exact action_x5
  · exact action_x6
  · exact action_x7
  · exact action_x8
  · exact action_x9
  · exact action_x10
  · exact action_x11
  · exact action_x12

lemma action_y0 : subgroupY⁻¹ * basis 0 * subgroupY =
    maskProduct basis 1 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask1]
  exact eval_conj representation eval_basis0 representation_y
    (decoded_common product_actiony0left product_actiony0right)

lemma action_y1 : subgroupY⁻¹ * basis 1 * subgroupY =
    maskProduct basis 4 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask4]
  exact eval_conj representation eval_basis1 representation_y
    (decoded_common product_actiony1left product_actiony1right)

lemma action_y2 : subgroupY⁻¹ * basis 2 * subgroupY =
    maskProduct basis 8 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask8]
  exact eval_conj representation eval_basis2 representation_y
    (decoded_common product_actiony2left product_actiony2right)

lemma action_y3 : subgroupY⁻¹ * basis 3 * subgroupY =
    maskProduct basis 2 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask2]
  exact eval_conj representation eval_basis3 representation_y
    (decoded_common product_actiony3left product_actiony3right)

lemma action_y4 : subgroupY⁻¹ * basis 4 * subgroupY =
    maskProduct basis 32 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask32]
  exact eval_conj representation eval_basis4 representation_y
    (decoded_common product_actiony4left product_actiony4right)

lemma action_y5 : subgroupY⁻¹ * basis 5 * subgroupY =
    maskProduct basis 128 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask128]
  exact eval_conj representation eval_basis5 representation_y
    (decoded_common product_actiony5left product_actiony5right)

lemma action_y6 : subgroupY⁻¹ * basis 6 * subgroupY =
    maskProduct basis 256 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask256]
  exact eval_conj representation eval_basis6 representation_y
    (decoded_common product_actiony6left product_actiony6right)

lemma action_y7 : subgroupY⁻¹ * basis 7 * subgroupY =
    maskProduct basis 16 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask16]
  exact eval_conj representation eval_basis7 representation_y
    (decoded_common product_actiony7left product_actiony7right)

lemma action_y8 : subgroupY⁻¹ * basis 8 * subgroupY =
    maskProduct basis 2048 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask2048]
  exact eval_conj representation eval_basis8 representation_y
    (decoded_common product_actiony8left product_actiony8right)

lemma action_y9 : subgroupY⁻¹ * basis 9 * subgroupY =
    maskProduct basis 4096 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask4096]
  exact eval_conj representation eval_basis9 representation_y
    (decoded_common product_actiony9left product_actiony9right)

lemma action_y10 : subgroupY⁻¹ * basis 10 * subgroupY =
    maskProduct basis 5964 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask5964]
  exact eval_conj representation eval_basis10 representation_y
    (decoded_common product_actiony10left product_actiony10right)

lemma action_y11 : subgroupY⁻¹ * basis 11 * subgroupY =
    maskProduct basis 64 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask64]
  exact eval_conj representation eval_basis11 representation_y
    (decoded_common product_actiony11left product_actiony11right)

lemma action_y12 : subgroupY⁻¹ * basis 12 * subgroupY =
    maskProduct basis 7428 := by
  apply representation_injective
  rw [map_maskProduct]
  simp only [representation_basis]
  rw [eval_mask7428]
  exact eval_conj representation eval_basis12 representation_y
    (decoded_common product_actiony12left product_actiony12right)

lemma basis_action_y (i : Fin 13) : subgroupY⁻¹ * basis i * subgroupY =
    maskProduct basis (yMasks i) := by
  fin_cases i
  · exact action_y0
  · exact action_y1
  · exact action_y2
  · exact action_y3
  · exact action_y4
  · exact action_y5
  · exact action_y6
  · exact action_y7
  · exact action_y8
  · exact action_y9
  · exact action_y10
  · exact action_y11
  · exact action_y12

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl
