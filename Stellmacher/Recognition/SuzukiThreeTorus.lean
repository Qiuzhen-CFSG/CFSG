module

public import Stellmacher.Recognition.SuzukiThreeSquareAction
public import Stellmacher.Recognition.SuzukiThreeSwapNontrivial

/-!
# Assembly of Suzuki's fifth-power torus action at q = 3

The square-action calculation reduces the desired swapping involution to the
existence of a swap acting nontrivially on the torus. The latter is the transfer
step of Suzuki (1965), Section II, Lemmas 3 and 6. The theorem below records
this reduction with its remaining hypothesis explicit.
-/

namespace Stellmacher.Recognition.SuzukiThreeHypotheses

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q)

include h

/-- Assembly once a swapping involution with nontrivial torus action is known. -/
public theorem exists_swap_pow_five_of_nontrivial (b : Ω) (hb : b ≠ a)
    (hswap : ∃ t : G, t ^ 2 = 1 ∧ t • a = b ∧ t • b = a ∧
      ∃ k : stabilizer (stabilizer G a) b,
        t⁻¹ * ((k : stabilizer G a) : G) * t ≠ ((k : stabilizer G a) : G)) :
    ∃ t : G, t ^ 2 = 1 ∧ t • a = b ∧ t • b = a ∧
      ∀ k : stabilizer (stabilizer G a) b,
        t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G) ^ 5 := by
  obtain ⟨t, ht, hta, htb, hne⟩ := hswap
  exact ⟨t, ht, hta, htb, h.swap_conj_eq_pow_five_of_ne b hb t hta htb hne⟩

/-- Suzuki's fifth-power action for every pair of distinct points.

The preceding square-action calculation leaves the identity and fifth-power
possibilities.  `exists_swap_nontrivial` is the transfer argument excluding
the identity possibility, and the assembly theorem then supplies the desired
swapping involution and its action on the two-point torus.
-/
public theorem exists_swap_pow_five [FaithfulSMul G Ω] (b : Ω) (hb : b ≠ a) :
    ∃ t : G, t ^ 2 = 1 ∧ t • a = b ∧ t • b = a ∧
      ∀ k : stabilizer (stabilizer G a) b,
        t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G) ^ 5 := by
  exact h.exists_swap_pow_five_of_nontrivial b hb (h.exists_swap_nontrivial b hb)

end Stellmacher.Recognition.SuzukiThreeHypotheses
