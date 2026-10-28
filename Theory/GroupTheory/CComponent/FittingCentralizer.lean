module

public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.Fitting.Centralizer

/-!
# C-components centralized by the Fitting subgroup

A C-component K of a finite group is quasisimple if F(G) centralizes K.
Subnormal monotonicity of the prime cores first gives F(K) ≤ F(G).
Since the solvable radical R of K is self-centralizing on F(R), centrality
of F(K) forces R = Z(K). The simple radical quotient of a C-component
then gives its simple central quotient.

This is the structural deduction used just before Aschbacher–Smith
Lemma 13.8.15, combined manuscript of 1 March 2004, printed p.952.
It does not assert that the local Fitting-centralizer hypothesis holds.
-/

@[expose] public section

open Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The Fitting subgroup of a subnormal subgroup maps into the ambient Fitting subgroup. -/
theorem fittingSubgroup_map_subtype_le_of_isSubnormal (K : Subgroup G) (hK : K.IsSubnormal) :
    (fittingSubgroup K).map K.subtype ≤ fittingSubgroup G := by
  rw [fitting_eq_sup_pCore K, Subgroup.map_iSup]
  refine iSup_le fun p => ?_
  let : Fact p.val.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.val.property⟩
  exact (pCoreIn_le_of_subnormal p.val.val hK).trans (pCore_le_fitting G p.val.val)

/-- A finite group with central Fitting subgroup has central solvable radical. -/
theorem solvableRadical_le_center_of_fitting_le_center
    (hf : fittingSubgroup G ≤ center G) : solvableRadical G ≤ center G := by
  let R := solvableRadical G
  have hFR : (fittingSubgroup R).map R.subtype ≤ fittingSubgroup G :=
    fittingSubgroup_map_subtype_le_of_isSubnormal R (inferInstance : R.Normal).isSubnormal
  have hRF : R ≤ (fittingSubgroup R).map R.subtype := by
    intro r hr
    have hc : (⟨r, hr⟩ : R) ∈ centralizer (fittingSubgroup R : Set R) := by
      apply mem_centralizer_iff.mpr
      intro f hfm
      apply Subtype.ext
      exact (mem_center_iff.mp (hf (hFR (mem_map.mpr ⟨f, hfm, rfl⟩))) r).symm
    have hrF := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable
      (G := R) inferInstance hc
    exact mem_map.mpr ⟨⟨r, hr⟩, hrF, rfl⟩
  exact hRF.trans (hFR.trans hf)

/-- A C-component is quasisimple when the ambient Fitting subgroup centralizes it. -/
theorem IsCComponent.isQuasisimple_of_fitting_centralizes {K : Subgroup G} (hK : K.IsCComponent)
    (hc : fittingSubgroup G ≤ centralizer (K : Set G)) : IsQuasisimple K := by
  have hf : fittingSubgroup K ≤ center K := by
    intro k hk
    apply mem_center_iff.mpr
    intro l
    apply Subtype.ext
    exact mem_centralizer_iff.mp
      (hc (fittingSubgroup_map_subtype_le_of_isSubnormal K hK.subnormal (mem_map.mpr ⟨k, hk, rfl⟩))) l l.property
  have hr : solvableRadical K = center K := by
    apply le_antisymm (solvableRadical_le_center_of_fitting_le_center hf)
    exact le_solvableRadical (center K) inferInstance
      (Group.isSolvable_of_comm (fun a b => Subtype.ext
        (mem_center_iff.mp a.property b).symm))
  let := hK.perfect
  let := hK.isSimpleGroup_quotient_solvableRadical
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩

end Subgroup

end
