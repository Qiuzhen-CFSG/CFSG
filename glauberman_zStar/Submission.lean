import Mathlib
import Submission.OddIndex
import Submission.CyclicCase
import Submission.BrauerSuzuki
import Submission.ZStar.OddCore
import Submission.ZStar.LocalReduction
import Submission.ZStar.CoreFree
import Submission.ZStar.QuotientReduction

set_option autoImplicit false

namespace Submission

open Subgroup

/-- Glauberman's Z*-theorem.

The proof uses the uniform Z*-theorem approach: convert global isolation to
Sylow-local data (Phase B), apply the local theorem (Phases C-D reducing to
the core-free case), and package the result via the odd-core/quotient bridge
(Phase A).

The core-free case (`glauberman_zstar_corefree`) is supplied by the uniform
principal-`2`-block factory and its strong-induction assembly. -/
theorem glauberman_zStar (G : Type) [Group G] [Fintype G]
    (t : G) (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hisolated : ∀ g : G,
      (g * t * g⁻¹) * t = t * (g * t * g⁻¹) →
        g * t * g⁻¹ = t) :
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- Normalize the involution hypotheses
  have htI : ZStar.IsInvolution t := ⟨ht1, by rw [pow_two, ht2]⟩
  -- Phase B: Convert global isolation to Sylow-local data
  obtain ⟨S, htS, htCentral, htWeak⟩ :=
    ZStar.isolated_involution_local_data t ht2 ht1 hisolated
  -- Phases C-E: Apply the local Z*-theorem
  have h_center := ZStar.glauberman_zstar_local S t htI htS htCentral htWeak
  -- Phase A: Package the result via the odd core
  exact ZStar.conclusion_of_mem_center_oddCore h_center

end Submission
