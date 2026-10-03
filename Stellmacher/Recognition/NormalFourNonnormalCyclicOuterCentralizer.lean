module

public import Stellmacher.Recognition.NormalFourNonnormalCoreSetup
public import Theory.GroupTheory.NormalFourWeaklyClosedInvolution

/-!
# Excluding an outside conjugate in the cyclic-tail branch

Weak closure of a central involution in the actual core preimage implies
weak closure in the Sylow subgroup. The normal four lies in the core
preimage, and `NormalFourWeaklyClosedInvolution` extends weak closure from
that four to the Sylow subgroup using commuting square roots.

Thus an outside conjugate gives a contradiction and, in particular, the
elementary-eight obstruction needed by the cyclic-tail assembly. The
strong bound on all elementary subgroup orders makes the cyclic Hall
factors and their orders unnecessary for this step. No bound on the core
order or its Sylow index is assumed.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, Case 2, p.393;
`refs/original/n-group-global/odd-core-rank-two-source/normal-four-case-split.md`.
The source's choice of a Sylow subgroup in `C_N(t)` is bypassed by transporting
a commuting square root through `C_G(z)`; the two centralizers are not identified.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- Weak closure in the actual core preimage extends to the whole Sylow
when its normal four is unique. -/
public theorem eq_of_isConj_of_weakly_closed_in_omegaCorePreimage
    (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (z : S) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (hweak : ∀ t : S, t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z)
    (t : S) (hconj : IsConj (z : G) (t : G)) : t = z := by
  apply S.eq_of_isConj_of_weakly_closed_in_unique_normal_four
    hrank E hE hunique z hzC hz ?_ t hconj
  intro u hu
  exact hweak u (four_le_omegaCorePreimage hN hrank S hZ E hE hu)

/-- An outside conjugate under core weak closure gives the elementary-eight
obstruction. This includes every cyclic-tail decomposition in the task,
without needing its factor orders, width, or a Sylow-index bound. -/
public theorem exists_elementary_eight_of_conjugate_outside_omegaCorePreimage
    (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hweak : ∀ z t : S, z ∈ center S → orderOf z = 2 →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z)
    (z t : S) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (ht : t ∉ omegaCorePreimage S) (hconj : IsConj (z : G) (t : G)) :
    ∃ U : Subgroup S, IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U := by
  have htz := eq_of_isConj_of_weakly_closed_in_omegaCorePreimage
    hN hrank S hZ E hE hunique z hzC hz (fun u => hweak z u hzC hz) t hconj
  have hzE : z ∈ E := mem_four_of_square_eq_one_of_elementary_card_lt_eight
    (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) E hE
    (by simpa only [hz] using pow_orderOf_eq_one z) (center_le_centralizer _ hzC)
  exact (ht (htz ▸ four_le_omegaCorePreimage hN hrank S hZ E hE hzE)).elim

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
