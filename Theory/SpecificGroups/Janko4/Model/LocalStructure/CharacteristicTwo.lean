module

public import Theory.Quasithin.EvenCharacteristic
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.Conjugacy

/-!
# Self-centralizing two-cores in the concrete J₄ max1 and max2 subgroups

For max1, the certified elementary kernel equals the intrinsic two-core and
is its own centralizer. For max2, the certified relative seed normal closure
is a normal two-group and contains its centralizer. Enlarging it to the
intrinsic two-core preserves that centralizer bound. The actual conjugacy
equivalence then transfers the result to the original ATLAS word subgroup.

These are intrinsic assertions about the two specified generated subgroups.
They require neither the order or simplicity of the ambient model nor an
identification of max2 with the entire ambient involution centralizer.
Exhaustive coverage of local overgroups and the max4 calculation are separate.

Source: GLS, Number 3, Table 5.3i, printed p.270. The literal ATLAS programs,
provenance and matrix certificates are retained in the imported modules.
The consumer is Aschbacher–Smith, Theorem 0.1.2(5), printed p.4, with
condition E defined on pp.3–4 and again on pp.481–482.
-/

public section

namespace Janko4.LocalStructure
open Subgroup

/-- The certified elementary kernel equals the intrinsic two-core of max1. -/
theorem max1_twoCore_centralizer_le :
    centralizer (pCore 2 (Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four) :
      Set (Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four)) ≤
        pCore 2 (Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four) := by
  intro x hx
  rw [← localKernel_eq_twoCore matrixA_mul_self matrixB_pow_four] at hx ⊢
  rwa [centralizer_localKernel] at hx

open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData in
/-- The normal two-subgroup certified in the conjugated max2 words is
self-centralizing; conjugation transports this to the original word subgroup. -/
theorem max2_twoCore_centralizer_le :
    centralizer (pCore 2 sourceSubgroup : Set sourceSubgroup) ≤ pCore 2 sourceSubgroup := by
  have hQ : localNormalClosure ≤ pCore 2 localSubgroup :=
    le_sSup ⟨inferInstance, localNormalClosure_isPGroup⟩
  have hc : centralizer (localNormalClosure : Set localSubgroup) ≤ localNormalClosure := by
    simpa only [localNormalClosureAction_ker] using localNormalClosureAction_ker_le
  have hlocal : centralizer (pCore 2 localSubgroup : Set localSubgroup) ≤
      pCore 2 localSubgroup := by
    intro x hx
    exact hQ (hc ((centralizer_le hQ) hx))
  exact (@Theory.Quasithin.centralizer_pCore_le_iff sourceSubgroup localSubgroup
    sourceSubgroup.toGroup localSubgroup.toGroup 2 sourceSubgroupEquivLocal).mpr hlocal

end Janko4.LocalStructure
