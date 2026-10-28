module
public import Theory.GroupTheory.CComponent.InvolutionCore
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Involutions with a solvable supplement to a C-component

A normal nonquasisimple C-component with solvable quotient leaves no
ordinary component in the whole group. An involution centralizing the
two-core and odd core therefore centralizes the full generalized Fitting
subgroup. It lies in the Fitting subgroup, hence in its normal Sylow
two-subgroup. The involution need not belong to the selected C-component.

Source application: Aschbacher--Smith 1.2.11 in 14.2.15, p.985.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {D : Type*} [Group D] [Finite D]

/-- With no ordinary component, an involution centralizing both complementary
cores lies in the two-core. -/
theorem involution_mem_twoCore_of_layer_eq_bot
    (hE : componentLayer D = ⊥) (z : D) (hz : orderOf z = 2)
    (hc2 : z ∈ centralizer (pCore 2 D : Set D))
    (hco : z ∈ centralizer (pPrimeCore 2 D : Set D)) : z ∈ pCore 2 D := by
  have hzf : z ∈ fittingSubgroup D := by
    have hc : zpowers z ≤ centralizer (fittingSubgroup D : Set D) := by
      apply subgroup_le_centralizer_fitting_of_le_centralizer_pCores
      intro q
      apply zpowers_le.mpr
      by_cases hq : q.val.val = 2
      · exact hq ▸ hc2
      · have ho : pCore q.val.val D ≤ pPrimeCore 2 D := by
          apply le_sSup
          refine ⟨inferInstance,?_⟩
          let : Fact q.val.val.Prime := ⟨Nat.prime_of_mem_primeFactors q.val.property⟩
          obtain ⟨n,hn⟩ := (pCore_isPGroup (p := q.val.val) (G := D)).exists_card_eq
          rw [hn]
          exact ((Nat.coprime_primes Nat.prime_two
            (Nat.prime_of_mem_primeFactors q.val.property)).mpr (Ne.symm hq)).pow_right _
        exact centralizer_le ho hco
    have hf : generalizedFitting D = fittingSubgroup D := by
      rw [generalizedFitting,hE,sup_bot_eq]
    exact hf ▸ centralizer_generalizedFitting_le D (hf.symm ▸ hc (mem_zpowers z))
  let zF : fittingSubgroup D := ⟨z,hzf⟩
  have hp : IsPGroup 2 (zpowers zF) := by
    let : IsElementaryAbelian 2 (zpowers zF) := by
      apply IsElementaryAbelian.zpowers_of_pow_eq_one
      apply Subtype.ext
      exact hz ▸ pow_orderOf_eq_one z
    exact IsElementaryAbelian.isPGroup 2 _
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  exact Sylow.map_le_pCore (inferInstance : (fittingSubgroup D).Normal) inferInstance 2 P
    (mem_map_of_mem _ (hP (mem_zpowers zF)))

omit [Finite D] in
/-- A normal nonquasisimple C-component with solvable quotient exhausts all
possible ordinary components. -/
theorem IsCComponent.layer_eq_bot_of_solvable_quotient
    {B : Subgroup D} [B.Normal] [Group.IsSolvable (D ⧸ B)]
    (hB : B.IsCComponent) (hn : ¬ IsQuasisimple B) : componentLayer D = ⊥ := by
  apply sSup_eq_bot.mpr
  intro L hL
  let := hL.2
  have hLB : L ≤ B := le_of_isPerfect_of_solvable_quotient L B
  have he := hL.isCComponent.eq_of_le hB hLB
  exact (hn (he ▸ hL.2)).elim
end Subgroup
