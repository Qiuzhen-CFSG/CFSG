module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal.Certificates.Case0
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal.Certificates.Case1
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal.Certificates.Case2
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal.Certificates.Case3
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal.Certificates.Case4
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal.Certificates.Case5
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal.Certificates.Case6
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal.Certificates.Case7
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal.Certificates.Case8
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal.Certificates.Case9

/-!
Checked odd-product witnesses on the original Janko matrix carrier.
This block shares short representation evaluations and checks every packed
product in the kernel. The words are from the literal ATLAS J4G1-max1W1
and transported max2 generators; source context: GLS3 Table 5.3i.
Ported from the checked GenerationAll witness of 7 October 2026.
-/

public section
namespace Janko4.AdequateLocal.Certificates
open Janko4 Janko4.Cardinality Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations Janko4.GeneratorCertificates
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true

@[expose] def fusionWord (i : Fin 10) : Model :=
  ![word0,word1,word2,word3,c,word2,word1,word2,word2,word9] i

@[expose] def fusionTarget (i : Fin 10) : Model :=
  ![pair,seed,seed,seed,seed,seed,seed,seed,seed,pair] i

@[expose] def fusionExponent (i : Fin 10) : ℕ :=
  ![5,43,43,31,3,31,33,31,43,5] i

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localX localY
  localKernelSeed basis pair seed gp c y d word0 word1 word2 word3 word9

theorem all_odd_product_certificates (i : Fin 10) :
    ((Simplicity.Max1Fusion.outsideRepresentative matrixA_mul_self matrixB_pow_four i : Model) *
      (fusionWord i * fusionTarget i * (fusionWord i)⁻¹))^(fusionExponent i) = 1 := by
  fin_cases i
  · exact actual_case_0_odd_product
  · exact actual_case_1_odd_product
  · exact actual_case_2_odd_product
  · exact actual_case_3_odd_product
  · exact actual_case_4_odd_product
  · exact actual_case_5_odd_product
  · exact actual_case_6_odd_product
  · exact actual_case_7_odd_product
  · exact actual_case_8_odd_product
  · exact actual_case_9_odd_product

theorem fusionExponent_odd (i : Fin 10) : Odd (fusionExponent i) := by
  fin_cases i <;> decide +kernel

end Janko4.AdequateLocal.Certificates
