module

public import Theory.GroupTheory.CommutatorNoncentral

/-!
# Elementary reductions for pushing up in nonconstrained 2-locals

Aschbacher–Smith, *The Classification of Quasithin Groups* (1 March 2004),
§C.3, pp. 148–151. The first step of C.3.2 uses the normalizer bound on `V`
to show that a component outside `MH` acts nontrivially on `V`, hence on `M₀`.
The result below isolates this step with its exact subgroup hypotheses.

The full configuration theorem C.3.1 additionally requires the component
reduction and the Lie-type and sporadic local analyses; it is not asserted here.
-/

namespace CFSG.Quasithin.ChapterC

variable {H : Type*} [Group H]

/-- The opening commutator reduction in C.3.2. The component property is only
needed upstream to establish `K ≰ MH` (C.2.10.2). -/
public theorem nontrivial_commutators_of_normalizer_le
    {V M₀ MH K : Subgroup H}
    (hVM : V ≤ M₀) (hnorm : Subgroup.normalizer (V : Set H) ≤ MH)
    (hK : ¬ K ≤ MH) :
    ⁅V, K⁆ ≠ ⊥ ∧ ⁅K, M₀⁆ ≠ ⊥ := by
  have hVK : ⁅V, K⁆ ≠ ⊥ := by
    intro hcomm
    apply hK
    exact (Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
      ((Subgroup.centralizer_le_normalizer (V : Set H)).trans hnorm)
  refine ⟨hVK, ?_⟩
  intro hKM
  apply hVK
  apply le_antisymm _ bot_le
  calc
    ⁅V, K⁆ ≤ ⁅M₀, K⁆ := Subgroup.commutator_mono hVM le_rfl
    _ = ⁅K, M₀⁆ := Subgroup.commutator_comm M₀ K
    _ = ⊥ := hKM

end CFSG.Quasithin.ChapterC
