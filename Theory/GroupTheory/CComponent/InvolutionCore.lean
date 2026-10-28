module
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.CComponent.FittingCentralizer
public import Theory.PPrimeCore


/-!
# Involutions in nonquasisimple C-components

A nonquasisimple C-component has trivial component layer. Its generalized
Fitting subgroup is therefore its Fitting subgroup and is self-centralizing.
An involution centralizing both the ambient two-core and odd core centralizes
each prime core of the C-component, so belongs to its Fitting subgroup and
then to its two-core. Subnormality embeds that core in the ambient two-core.

This is the component reduction in Aschbacher–Smith 1.2.11, printed p.508.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A nonquasisimple C-component has no ordinary component. -/
theorem IsCComponent.layer_eq_bot_of_not_quasisimple {K : Subgroup G}
    (hK : K.IsCComponent) (hn : ¬ IsQuasisimple K) : componentLayer K = ⊥ := by
  apply bot_unique
  apply sSup_le
  intro A hA
  have he := hK.eq_top_of_isCComponent hA.isCComponent
  have hq : IsQuasisimple K := by
    let := hA.2
    exact IsQuasisimple.of_mulEquiv ((MulEquiv.subgroupCongr he).trans Subgroup.topEquiv)
  exact (hn hq).elim

/-- An involution in a nonquasisimple C-component lies in the ambient two-core
when it centralizes both the ambient two-core and odd core. -/
theorem IsCComponent.involution_mem_twoCore {K : Subgroup G}
    (hK : K.IsCComponent) (hn : ¬ IsQuasisimple K) (z : K) (hz : orderOf z = 2)
    (hc2 : (z : G) ∈ centralizer (pCore 2 G : Set G))
    (hco : (z : G) ∈ centralizer (pPrimeCore 2 G : Set G)) : (z : G) ∈ pCore 2 G := by
  have hf : z ∈ fittingSubgroup K := by
    have hc : z ∈ centralizer (fittingSubgroup K : Set K) := by
      have hh : zpowers z ≤ centralizer (fittingSubgroup K : Set K) := by
        apply subgroup_le_centralizer_fitting_of_le_centralizer_pCores
        intro q
        apply zpowers_le.mpr
        intro x hx
        apply Subtype.ext
        have hm : (x : G) ∈ pCore q.val.val G :=
          pCoreIn_le_of_subnormal q.val.val hK.subnormal (mem_map_of_mem K.subtype hx)
        by_cases hq : q.val.val = 2
        · exact hc2 x (hq ▸ hm)
        · have ho : pCore q.val.val G ≤ pPrimeCore 2 G := by
            apply le_sSup
            refine ⟨inferInstance,?_⟩
            let : Fact q.val.val.Prime := ⟨Nat.prime_of_mem_primeFactors q.val.property⟩
            obtain ⟨n,hn⟩ := (pCore_isPGroup (p := q.val.val) (G := G)).exists_card_eq
            rw [hn]
            exact ((Nat.coprime_primes Nat.prime_two (Nat.prime_of_mem_primeFactors q.val.property)).mpr
              (Ne.symm hq)).pow_right _
          exact hco x (ho hm)
      exact hh (mem_zpowers z)
    have he : generalizedFitting K = fittingSubgroup K := by
      rw [generalizedFitting,hK.layer_eq_bot_of_not_quasisimple hn,sup_bot_eq]
    exact he ▸ centralizer_generalizedFitting_le K (he.symm ▸ hc)
  let zF : fittingSubgroup K := ⟨z,hf⟩
  have hp : IsPGroup 2 (zpowers zF) := by
    let : IsElementaryAbelian 2 (zpowers zF) := by
      apply IsElementaryAbelian.zpowers_of_pow_eq_one
      apply Subtype.ext
      exact hz ▸ pow_orderOf_eq_one z
    exact IsElementaryAbelian.isPGroup 2 _
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  have hzK : z ∈ pCore 2 K :=
    Sylow.map_le_pCore (inferInstance : (fittingSubgroup K).Normal) inferInstance 2 P
      (mem_map_of_mem _ (hP (mem_zpowers zF)))
  exact pCoreIn_le_of_subnormal 2 hK.subnormal (mem_map_of_mem K.subtype hzK)

end Subgroup
