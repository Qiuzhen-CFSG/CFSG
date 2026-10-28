module

public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import Theory.GroupTheory.SelfCentralizingCore

/-!
# Self-centralizing prime cores determine the generalized Fitting subgroup

If O_p(G) contains its centralizer, the same holds in every subnormal
subgroup. In a quasisimple component its p-core is central, which would
make the component abelian. Thus the layer is trivial. The p'-core is
also trivial, and the Fitting subgroup is O_p(G).

This is the equivalence of the two characteristic-p conventions used
in Aschbacher–Smith, Definitions 1.1.1 and A.4.5, printed pp.500 and 58.
The argument follows the component calculus, with no classification input.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- A self-centralizing p-core is the entire generalized Fitting subgroup. -/
theorem generalizedFitting_eq_pCore_of_selfCentralizing [Finite G] (p : ℕ) [Fact p.Prime]
    (hc : centralizer (pCore p G : Set G) ≤ pCore p G) :
    generalizedFitting G = pCore p G := by
  have he : componentLayer G = ⊥ := by
    apply sSup_eq_bot.mpr
    intro K hK
    let := hK.2
    have hk := subnormal_core_selfCentralizing hc K hK.1
    have hz := IsQuasisimple.pCore_le_center (G := K) p
    have ht : (⊤ : Subgroup K) ≤ center K := by
      calc
        ⊤ = centralizer (center K : Set K) := centralizer_center.symm
        _ ≤ centralizer (pCore p K : Set K) := centralizer_le hz
        _ ≤ center K := hk.trans hz
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    exact (Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp (top_unique ht))).elim
  rw [generalizedFitting, he, sup_bot_eq, Fitting_eq_pcore G p
    (pPrimeCore_eq_bot_of_centralizer_pCore_le p hc)]

end Theory.GroupTheory
end
