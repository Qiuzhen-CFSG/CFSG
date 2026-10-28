module
public import Theory.GroupTheory.GeneralizedFitting.CentralizerQuotient

/-!
# The faithful image of a normal quasisimple subgroup

A self-centralizing normal quasisimple subgroup is the whole generalized
Fitting subgroup: the Fitting subgroup centralizes it, and every other
component centralizes it. Factoring by its centralizer gives precisely this
situation, without imposing a restriction on the outer quotient.

This is the almost-simple section used before Aschbacher–Smith A.3.15 in
Proposition 1.3.4, printed pp.510–511.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem generalizedFitting_eq_of_quasisimple_centralizer
    (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hC : centralizer (L : Set G) = ⊥) : generalizedFitting G = L := by
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hL : IsComponent G L := ⟨(inferInstance : L.Normal).isSubnormal, inferInstance⟩
  apply le_antisymm _ (component_le_generalizedFitting G L hL)
  apply sup_le
  · rcases hL.normal_dichotomy (fittingSubgroup G) with hf | hf
    · have : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
        (f := inclusion hf) (inclusion_injective hf)
      exact (Group.IsPerfect.not_isSolvable L this).elim
    · rw [commutator_comm] at hf
      exact (commutator_eq_bot_iff_le_centralizer.mp hf).trans (hC.le.trans bot_le)
  · apply sSup_le
    intro K hK
    by_cases hk : K = L
    · exact hk.le
    · have hh := hK.commutator_eq_bot_of_ne hL hk
      exact (commutator_eq_bot_iff_le_centralizer.mp hh).trans (hC.le.trans bot_le)

/-- Factoring by the centralizer makes a normal quasisimple subgroup the
whole generalized Fitting subgroup, without a restriction on the outer quotient. -/
theorem centralizerQuotient_generalizedFitting_unrestricted
    (L : Subgroup G) [L.Normal] [IsQuasisimple L] :
    generalizedFitting (CentralizerQuotient L) = centralizerQuotientComponent L := by
  let q := centralizerQuotientMap L
  let D := centralizerQuotientComponent L
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let : D.Normal := (inferInstance : L.Normal).map q hq
  let : IsSimpleGroup D := centralizerQuotientComponent_simple L
  let : IsQuasisimple D := IsQuasisimple.of_surjective (q.subgroupMap L)
    (q.subgroupMap_surjective L)
  exact generalizedFitting_eq_of_quasisimple_centralizer D
    (centralizerQuotientComponent_centralizer L)
end Theory.GroupTheory
