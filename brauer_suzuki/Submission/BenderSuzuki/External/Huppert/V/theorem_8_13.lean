/-
Authors: OpenAI
-/

module

public import Submission.BenderSuzuki.External.Huppert.V.theorem_8_12
public import Submission.BenderSuzuki.External.Huppert.V.ComplementTransfer

/-!
# Huppert V.8.13

Book-order entry file for the minimal-counterexample and invariant Sylow
normal-complement machinery used by Thompson V.8.14.

Principal exported declarations include:
* `hkt_maximal_invariant_quotient_exists_isElementaryAbelian`
* `hkt_maximal_lower_nilpotent_exists_isPGroup`
* `hkt_false_of_same_prime_lower_and_quotient_pgroups`
* `hkt_false_of_solvable_maximal_branch_core`
* `hkt_exists_invariant_sylow_of_prime_period`
* `hkt_normalizer_thompsonSubgroup_has_normal_p_complement_of_invariant_odd_sylow`
-/

namespace BenderSuzuki
namespace External


universe u
/-- Huppert V.8.13, minimal-counterexample contradiction interface. -/
public theorem huppert_V_8_13_false_of_solvable_maximal_branch_core
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p : ℕ}
    (hprime : Nat.Prime p) (hp2 : p ≠ 2)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1)
    (hnon_nil : ¬ Group.IsNilpotent Q)
    (hsolv : IsSolvable Q)
    (N : Subgroup Q) [N.Normal]
    (hNinv : IsInvariant (Subgroup.zpowers φ) Q N)
    (hN_ne_bot : N ≠ ⊥) (hN_ne_top : N ≠ ⊤)
    (hNmax :
      ∀ K : Subgroup Q, K.Normal → IsInvariant (Subgroup.zpowers φ) Q K →
        N ≤ K → K ≠ ⊤ → K = N)
    (hN_nil : Group.IsNilpotent N)
    (hquot_nil : Group.IsNilpotent (Q ⧸ N))
    (hproper_invariant_quotient_nil :
      ∀ K : Subgroup Q, [K.Normal] → K ≠ ⊥ → K ≠ ⊤ →
        (∀ q : Q, q ∈ K ↔ φ q ∈ K) → Group.IsNilpotent (Q ⧸ K))
    (hcenter_bot : Subgroup.center Q = ⊥) :
    False :=
  hkt_false_of_solvable_maximal_branch_core
    (Q := Q) (φ := φ) (p := p) hprime hp2 hperiod hprod hnon_nil hsolv
    N hNinv hN_ne_bot hN_ne_top hNmax hN_nil hquot_nil
    hproper_invariant_quotient_nil hcenter_bot

end External
end BenderSuzuki
