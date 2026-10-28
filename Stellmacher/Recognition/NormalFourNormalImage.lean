module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Stellmacher.Recognition.NormalFourMovingConjugate
public import Stellmacher.Recognition.NormalFourWeakClosure
public import Theory.GroupTheory.PGroup.RankTwoNormalFourTransfer

/-!
# Excluding the normal odd-core image branch

Let `E` be the unique normal four-group of a Sylow two-subgroup `S`, with
one central involution. Thompson transfer and the rank bound imply that
every Sylow involution has an ambient conjugate in `E`.

If the image of `E` in `N/O₂′(N)`, where `N = N_G(Ω₁(Z(S)))`, is normal,
a conjugator in `N` carrying `E` back into `S` preserves `E`. The proof uses
injectivity of the quotient map on the Sylow subgroup, and does not assume
that `E` is normal in `N`.

The transport argument in `NormalFourMovingConjugate` extends this to every
conjugator carrying `E` back into `S`, so `E` is weakly closed. In a
nonsolvable finite simple group, `NormalFourWeakClosure` rules this out by
Z-star and Hall transfer, treating both the fused and separated involution
cases. Thus the quotient image cannot be normal. The rank bound makes the
N₂ hypothesis and a separate noncommutativity assumption unnecessary here.

Source: Janko–Thompson, Math. Z. 113 (1970), §§3 and 6, pp.387–389 and 395.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

open Subgroup
open scoped IsMulCommutative

private theorem no_normal_index_two
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN hi
  rcases hN.eq_bot_or_eq_top with hbot | htop
  · have hcard : Nat.card G = 2 := by simpa [hbot] using hi
    let : IsCyclic G := isCyclic_of_prime_card hcard
    exact hns (Group.isSolvable_of_comm (fun a b => mul_comm a b))
  · simp [htop] at hi

/-- The normal four-group meets every ambient involution class in the Sylow. -/
public theorem involution_isConj_mem_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) (t : S) (ht : orderOf t = 2) :
    ∃ u : S, u ∈ E ∧ IsConj (t : G) (u : G) :=
  S.exists_isConj_mem_normal_four_of_elementary_card_lt_eight
    (no_normal_index_two hns) hrank hZ E hE t ht

/-- The unique normal four cannot have normal image modulo the odd core of
the central-omega normalizer. Normality is assumed only after quotienting. -/
public theorem false_of_normal_fourImage
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    [(fourImage S E).Normal] : False :=
  false_of_weakly_closed hns hrank S hZ E hE hunique
    (conjugate_four_eq_of_normal_fourImage hrank S hZ E hE hunique)

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
