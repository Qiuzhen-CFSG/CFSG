module

public import GorensteinWalter.BrauerSuzukiWallCardTwoNormalizer
public import GorensteinWalter.BrauerSuzukiWallCardTwoA5

/-!
# The order-four centralizer branch of I.4.1

The order-two Brauer–Suzuki–Wall rotation subgroup gives precisely `A₄`
or `A₅`. The normalizer calculation handles the first alternative, and
the faithful action on five cosets handles the second. In particular this
interface retains the nonsimple `A₄` case.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.4.1(1),
printed p. 415; the checked Brauer–Suzuki–Wall proofs are reused directly.
Constructing the Brauer–Suzuki–Wall data from the dihedral centralizer
hypotheses is a separate prerequisite.
-/

namespace CFSG.Quasithin
open GorensteinWalter

/-- The two concrete isomorphism alternatives when the BSW rotation subgroup has order two. -/
public theorem alternating_four_or_five_of_bsw_card_two
    {G : Type*} [Group G] [Finite G] (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 2) :
    Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  by_cases hN : Subgroup.normalizer (h.H : Set G) = ⊤
  · left
    have eN := h.normalizer_mulEquiv_alternatingGroup_four_of_card_K_eq_two hk
    rw [hN] at eN
    exact ⟨Subgroup.topEquiv.symm.trans eN.some⟩
  · exact Or.inr
      (h.mulEquiv_alternatingGroup_five_of_card_K_eq_two_of_normalizer_ne_top hk hN)

end CFSG.Quasithin
