module

public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.JankoFour.PrimeKernel
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal.Marking
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.Action
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension.Matrix

/-!
# The two intrinsic local E-generation bounds for Janko four

The actual max1 subgroup has elementary two-core of order 2048 and quotient
M24, so a bound for M24 lifts through that core. The full first involution
centralizer has intrinsic quotient 3.M22.2. Its normal scalar subgroup has
order three, and the quotient by that scalar is the native Aut(M22).
PrimeKernel discharges this odd kernel; normal-two-subgroup lifting then
discharges the centralizer's intrinsic two-core. The explicit conjugator
identifies this centralizer with the marked max1-pair centralizer used in
the generating amalgam.

Only the E-generation bounds for M24 and Aut(M22) remain hypotheses.
In particular no replacement of 3.M22.2 by M22.2, splitting assumption,
order-based identification, or general composition-factor reduction is used.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
E.1.14(5), printed p.214, citing Asc82a Lemma 4.9; GLS3 Table 5.3i.
The actual ATLAS matrices and words retain their attribution in the imported
Janko4 modules.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.JankoFour
open Janko4 Janko4.Max1AmalgamRigidity

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  Janko4.Cardinality.max1Subgroup Janko4.Cardinality.localKernel
  Janko4.Cardinality.localX Janko4.Cardinality.localY Janko4.Cardinality.localKernelSeed

/-- Lift along the actual Mathieu quotient with its normal elementary two-kernel. -/
theorem mathieu_isEGenerated_of_m24 {i : ℕ}
    (h24 : IsEGenerated i Sporadic.Mathieu.M24) : IsEGenerated i M := by
  apply IsEGenerated.of_normal_two_subgroup K
  · exact IsPGroup.of_card (n := 11)
      (Janko4.Cardinality.localKernel_card matrixA_mul_self matrixB_pow_four)
  · exact h24.map_equiv
      (Janko4.LocalStructure.localQuotientEquivM24 matrixA_mul_self matrixB_pow_four).symm


end CFSG.Quasithin.ChapterE.JankoFour

open Subgroup
namespace CFSG.Quasithin.ChapterE.JankoFour
open Janko4 Janko4.Max1AmalgamRigidity

private theorem centralizer_map_conj (x g : Model) :
    (centralizer ({x} : Set Model)).map (MulAut.conj g).toMonoidHom =
      centralizer ({MulAut.conj g x} : Set Model) := by
  let f := MulAut.conj g
  apply le_antisymm
  · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
      map_centralizer_le_centralizer_image ({x} : Set Model) f.toMonoidHom
  · intro y hy
    refine mem_map.mpr ⟨f.symm y, mem_centralizer_singleton_iff.mpr ?_,
      f.apply_symm_apply y⟩
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using mem_centralizer_singleton_iff.mp hy

/-- Transport the marked max1-pair centralizer to the literal first-generator centralizer. -/
noncomputable def markedCentralizerEquivFirst : C ≃* InvolutionCentralizers.First.centralizer := by
  let g := AdequateLocal.Certificates.gp
  apply ((MulAut.conj g).subgroupMap C).trans
  apply MulEquiv.subgroupCongr
  change (centralizer ({AdequateLocal.Certificates.pair} : Set Model)).map
    (MulAut.conj g).toMonoidHom = _
  rw [centralizer_map_conj]
  change centralizer ({g * AdequateLocal.Certificates.pair * g⁻¹} : Set Model) = _
  rw [show g * AdequateLocal.Certificates.pair * g⁻¹ = a from
    AdequateLocal.gp_conj_pair]

/-- Both genuine kernels are discharged: the scalar of order three, then the intrinsic two-core. -/
theorem centralizer_isEGenerated_of_aut_m22 {i : ℕ} (hi : 1 ≤ i)
    (h22 : IsEGenerated i (MulAut Sporadic.Mathieu.M22)) : IsEGenerated i C := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hlinear : IsEGenerated i
      OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel.actionGroup :=
    IsEGenerated.of_normal_prime_order hi
      InvolutionCentralizers.First.QuotientExtension.scalarSubgroup
      InvolutionCentralizers.First.QuotientExtension.scalarSubgroup_card
      (h22.map_equiv InvolutionCentralizers.First.QuotientExtension.scalarQuotientEquiv.symm)
  have hfirst : IsEGenerated i InvolutionCentralizers.First.centralizer :=
    IsEGenerated.of_normal_two_subgroup
      (pCore 2 InvolutionCentralizers.First.centralizer) pCore_isPGroup
      (hlinear.map_equiv InvolutionCentralizers.First.quotientEquiv.symm)
  exact hfirst.map_equiv markedCentralizerEquivFirst.symm

end CFSG.Quasithin.ChapterE.JankoFour
