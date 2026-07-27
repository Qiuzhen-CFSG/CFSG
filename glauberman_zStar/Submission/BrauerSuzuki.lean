import Mathlib

import Submission.BenderSuzuki.PFAppendixII.proposition_1

open BenderSuzuki.PFAppendixIII

/-!
# Brauer-Suzuki Theorem

For groups with generalized quaternion Sylow 2-subgroups, the unique involution
lies in Z*(G). This is proved in the `brauer_suzuki` project at `../brauer_suzuki`.
We restate the theorem here for the Z*-theorem proof.
-/

namespace Submission.BrauerSuzuki

open Subgroup

/-- The odd core `O(G) = O_{2'}(G)`: the largest normal subgroup of odd order.

This definition matches the `pPrimeCore 2 G` from the Bender-Suzuki infrastructure
(since `Nat.Coprime 2 n ↔ Odd n`). -/
def oddCore (G : Type*) [Group G] : Subgroup G :=
  sSup {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)}

/-- The odd core equals `pPrimeCore 2 G`. -/
lemma oddCore_eq_pPrimeCore_two (G : Type*) [Group G] : oddCore G = pPrimeCore 2 G := by
  ext x; simp [oddCore, pPrimeCore, Nat.coprime_two_left]

/-- The odd core is normal (inherited from pPrimeCore). -/
instance oddCore_normal (G : Type*) [Group G] : (oddCore G).Normal := by
  rw [oddCore_eq_pPrimeCore_two G]
  exact pPrimeCore_normal (p := 2) (G := G)

/-- The Brauer-Suzuki theorem: If a Sylow 2-subgroup P is generalized quaternion
(of order 2^n with n ≥ 3), then any involution t ∈ P maps to the center of
G / oddCore G. -/
theorem brauer_suzuki {G : Type*} [Group G] [Finite G]
    (n : ℕ) (hn : 3 ≤ n)
    (P : Sylow 2 G)
    (hquat : Nonempty ((P : Subgroup G) ≃* QuaternionGroup (2 ^ (n - 2))))
    (t : G) (ht_mem : t ∈ (P : Subgroup G)) (ht_ord : orderOf t = 2) :
    (QuotientGroup.mk t : G ⧸ oddCore G) ∈
      Subgroup.center (G ⧸ oddCore G) := by
  -- Use the equality with pPrimeCore to get normality
  have hcore_eq : oddCore G = pPrimeCore 2 G := oddCore_eq_pPrimeCore_two G
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

end Submission.BrauerSuzuki
