module
public import Theory.GroupTheory.CComponent.FittingCentralizer
public import Theory.PPrimeCore

/-!
# Components in a nontrivial prime-complement core

If the Fitting subgroup of a finite group is a p-group, its p-complement
core has trivial Fitting subgroup. A nontrivial such core is therefore
nonsolvable and contains a C-component, which lifts through the normal
inclusion. The actual consumer is the original local quotient in
Aschbacher–Smith 14.7.7, printed p.1045.
-/

public section
open Subgroup Theory.GroupTheory

namespace Subgroup
variable {D : Type*} [Group D] [Finite D]
theorem exists_cComponent_le_primeComplement_of_fitting_isPGroup
    (p : ℕ) [Fact p.Prime]
    (hf : IsPGroup p (fittingSubgroup D)) (hne : pPrimeCore p D ≠ ⊥) :
    ∃ K : Subgroup D, K.IsCComponent ∧ K ≤ pPrimeCore p D := by
  let N := pPrimeCore p D
  have hdisj : Disjoint N (fittingSubgroup D) := by
    obtain ⟨n,hn⟩ := hf.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact pPrimeCore_coprime_card.symm.pow_right n
  have hfit : fittingSubgroup N = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ N.subtype_injective).mp
    exact bot_unique ((le_inf (map_subtype_le _) (fittingSubgroup_map_subtype_le_of_isSubnormal N
      (inferInstance : N.Normal).isSubnormal)).trans hdisj.eq_bot.le)
  have hnsolv : ¬ Group.IsSolvable N := by
    intro hs
    let := hs
    exact hne (card_eq_one.mp ((fitting_eq_bot_iff_card_eq_one_of_solvable N).mp hfit))
  obtain ⟨K,hK⟩ := exists_isCComponent_of_not_isSolvable hnsolv
  exact ⟨K.map N.subtype,hK.map_subtype (inferInstance : N.Normal).isSubnormal,map_subtype_le K⟩
end Subgroup
