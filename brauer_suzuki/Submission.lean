import ChallengeDeps
import Submission.BenderSuzuki.PFAppendixII.proposition_1

open LeanEval.GroupTheory
open LeanEval.GroupTheory.Defs
open BenderSuzuki.PFAppendixIII

namespace Submission

theorem brauer_suzuki {G : Type*} [Group G] [Finite G]
    (n : ℕ) (hn : 3 ≤ n)
    (P : Sylow 2 G)
    (hquat : Nonempty ((P : Subgroup G) ≃* QuaternionGroup (2 ^ (n - 2))))
    (t : G) (ht_mem : t ∈ (P : Subgroup G)) (ht_ord : orderOf t = 2) :
    (QuotientGroup.mk t : G ⧸ oddCore G) ∈
      Subgroup.center (G ⧸ oddCore G) := by
  have hcore_eq : oddCore G = pPrimeCore 2 G := by
    simp only [oddCore, pPrimeCore, Nat.coprime_two_left]
  have ht_inv : IsInvolution t := by
    have ht := (orderOf_eq_prime_iff (x := t) (p := 2)).mp ht_ord
    exact ⟨ht.2, ht.1⟩
  have hcentral :=
    BenderSuzuki.PFAppendixII.appendixII_quotient_involution_central_public
      P hn hquat t ht_inv
  rw [Subgroup.mem_center_iff] at hcentral ⊢
  intro z
  refine QuotientGroup.induction_on z (fun g => ?_)
  have hg := hcentral (QuotientGroup.mk' (pPrimeCore 2 G) g)
  change ((g * t : G) : G ⧸ oddCore G) = ((t * g : G) : G ⧸ oddCore G)
  apply QuotientGroup.eq_iff_div_mem.mpr
  rw [hcore_eq]
  apply QuotientGroup.eq_iff_div_mem.mp
  exact hg

end Submission
