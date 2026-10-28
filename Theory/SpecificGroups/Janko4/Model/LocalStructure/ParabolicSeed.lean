module
public import Theory.GroupTheory.TwoPerfectNormalizerControl
public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo

/-!
# A central-omega seed for a Sylow-invariant Janko subgroup

The native max1 and max4 subgroups have self-centralizing two-cores.
If a nontrivial subgroup N lies in one of them and is normalized by a
full ambient Sylow, the local two-core normalizes N. Its commutator with N
forces the intrinsic two-core of N to be nontrivial. Every actor normalizing
N consequently normalizes its nonzero elementary central-omega subgroup.

The source consumer JankoActorSeed uses the actual Y-normal closure and
its original projected actor. No containment of N in the actor is needed,
and solvability alone is not used to infer a nonzero two-core. This supplies
a seed for a subsequent elementary-normalizer cover; it does not prove
that cover or the original actor's normalizer containment.
Source: Aschbacher–Smith 12.5.4, printed p.819/PDF p.836.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ParabolicSeed

private theorem core_nontrivial (S : Sylow 2 Model) (M N : Subgroup Model)
    (hSM : (S : Subgroup Model) ≤ M) (hNM : N ≤ M)
    (hSN : (S : Subgroup Model) ≤ normalizer (N : Set Model)) (hne : N ≠ ⊥)
    (hc : centralizer (pCore 2 M : Set M) ≤ pCore 2 M) : pCore 2 N ≠ ⊥ := by
  have hQS : M.pCoreIn 2 ≤ (S : Subgroup Model) := by
    have hh := pCoreIn_le_sylow M (S.subtype hSM)
    rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le hSM] at hh
  exact pCore_ne_bot_of_core_normalizes M N hNM hc (hQS.trans hSN) hne

/-- A nontrivial Sylow-invariant subgroup contained in max1 or max4 has a
nonzero central-omega seed normalized by every actor normalizing that subgroup. -/
theorem elementary_seed (S : Sylow 2 Model) (N A : Subgroup Model)
    (hSA : (S : Subgroup Model) ≤ A) (hAN : A ≤ normalizer (N : Set Model))
    (hne : N ≠ ⊥)
    (hplace : (S : Subgroup Model) ⊔ N ≤
        Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four ∨
      (S : Subgroup Model) ⊔ N ≤ SymmetricLinear.max4Subgroup) :
    let E := omegaCenterIn (N.pCoreIn 2)
    pCore 2 N ≠ ⊥ ∧ E ≠ ⊥ ∧ IsElementaryAbelian 2 E ∧
      A ≤ normalizer (E : Set Model) := by
  have hcore : pCore 2 N ≠ ⊥ := by
    rcases hplace with hm | hm
    · apply core_nontrivial S _ N (le_sup_left.trans hm) (le_sup_right.trans hm)
        (hSA.trans hAN) hne
      rw [← localKernel_eq_twoCore matrixA_mul_self matrixB_pow_four]
      exact (centralizer_localKernel matrixA_mul_self matrixB_pow_four).le
    · exact core_nontrivial S _ N (le_sup_left.trans hm) (le_sup_right.trans hm)
        (hSA.trans hAN) hne SymmetricLinear.max4_twoCore_centralizer_le
  have hQ : N.pCoreIn 2 ≠ ⊥ := by
    intro he
    exact hcore ((map_eq_bot_iff_of_injective _ N.subtype_injective).mp he)
  have hE : omegaCenterIn (N.pCoreIn 2) ≠ ⊥ := by
    have hh := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup
      (N.pCoreIn 2) (N.pCoreIn 2) le_rfl (isPGroup_pCoreIn 2 N)
      (N.pCoreIn 2).le_normalizer hQ
    intro hz
    apply hh
    rw [hz, inf_bot_eq]
  exact ⟨hcore, hE, inferInstance,
    (hAN.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N))).trans
      (normalizer_le_normalizer_omegaCenterIn _)⟩

end Janko4.LocalStructure.ParabolicSeed
