module

public import Stellmacher.Recognition.NormalFourNonnormalCoreSetup
public import Stellmacher.Recognition.NormalFourNonnormalLargeNoncyclicTail
public import Theory.GroupTheory.PGroup.ExtraspecialCentralProduct

/-!
# Noncyclic Hall tails in the nonnormal four-group branch

The quotient is the actual odd-core quotient of the central-omega normalizer.
Its core has cyclic center. If an order-eight extraspecial factor has a
noncyclic commuting tail of order eight, the entire core is extraspecial of
order 32. Taking the whole core and the trivial subgroup as new Hall factors
contradicts intrinsic width one. The ambient fusion theorem excludes tails
of order at least sixteen. Since the tail has prime-power order, these two
exclusions give the strict bound of eight.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, Case 1, pp.392–393;
`refs/original/n-group-global/odd-core-rank-two-source/normal-four-case-split.md`.
-/

open Subgroup

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

/-- An order-eight noncyclic commuting tail would make the entire core an
extraspecial factor of order 32, contradicting intrinsic width one. -/
public theorem omegaQuotient_noncyclicHallTail_card_ne_eight
    {G : Type*} [Group G] [Finite G]
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (E : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (hwidth : ∀ A D : Subgroup (pCore 2 (OmegaQuotient S)),
      A.Normal → D.Normal → IsExtraspecial 2 A → IsBinaryHallFactor D →
      D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))) → A ⊔ D = ⊤ →
      Nat.card A ≠ 32)
    (A D : Subgroup (pCore 2 (OmegaQuotient S))) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] (hA : Nat.card A = 8) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hg : A ⊔ D = ⊤) : Nat.card D ≠ 8 := by
  intro hD
  let H := pCore 2 (OmegaQuotient S)
  let : IsCyclic (center H) :=
    omegaQuotient_pCore_center_isCyclic hrank S E hunique hnormal
  obtain ⟨hH, hcard⟩ := extraspecial_card_thirty_two_of_noncyclic_eight_factors
    pCore_isPGroup A D hA hD hn hc hg
  have htop : IsExtraspecial 2 (⊤ : Subgroup H) :=
    hH.of_mulEquiv Subgroup.topEquiv.symm
  have hbot : IsBinaryHallFactor (⊥ : Subgroup H) := Or.inl inferInstance
  apply hwidth ⊤ ⊥ inferInstance inferInstance htop hbot bot_le (top_sup_eq _)
  exact (Nat.card_congr Subgroup.topEquiv.toEquiv).trans hcard

/-- After the larger maximal-class tails have been excluded, the intrinsic
order-eight exclusion supplies the required strict tail bound. -/
public theorem omegaQuotient_noncyclicHallTail_card_lt_eight_of_card_lt_sixteen
    {G : Type*} [Group G] [Finite G]
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (E : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (hwidth : ∀ A D : Subgroup (pCore 2 (OmegaQuotient S)),
      A.Normal → D.Normal → IsExtraspecial 2 A → IsBinaryHallFactor D →
      D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))) → A ⊔ D = ⊤ →
      Nat.card A ≠ 32)
    (A D : Subgroup (pCore 2 (OmegaQuotient S))) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] (hA : Nat.card A = 8) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hg : A ⊔ D = ⊤) (hsmall : Nat.card D < 16) : Nat.card D < 8 := by
  have hne := omegaQuotient_noncyclicHallTail_card_ne_eight
    hrank S E hunique hnormal hwidth A D hA hn hc hg
  obtain ⟨n, hn⟩ :=
    ((pCore_isPGroup (p := 2) (G := OmegaQuotient S)).to_subgroup D).exists_card_eq
  have hnle : n ≤ 3 := by
    by_contra h
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show 4 ≤ n by omega)
    rw [← hn] at hp
    omega
  have hle : Nat.card D ≤ 8 := by
    rw [hn]
    exact Nat.pow_le_pow_right (by decide) hnle
  omega

/-- Intrinsic width one excludes every noncyclic Hall tail of order at least
eight, combining the whole-core extraspecial argument at order eight with
the ambient fusion exclusion for larger tails. -/
public theorem omegaQuotient_noncyclicHallTail_card_lt_eight
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (hwidth : ∀ A D : Subgroup (pCore 2 (OmegaQuotient S)),
      A.Normal → D.Normal → IsExtraspecial 2 A → IsBinaryHallFactor D →
      D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))) → A ⊔ D = ⊤ →
      Nat.card A ≠ 32)
    (A D : Subgroup (pCore 2 (OmegaQuotient S))) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] (hA : Nat.card A = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hg : A ⊔ D = ⊤) : Nat.card D < 8 := by
  exact omegaQuotient_noncyclicHallTail_card_lt_eight_of_card_lt_sixteen
    hrank S E hunique hnormal hwidth A D hA hn hc hg
    (omegaQuotient_noncyclicHallTail_card_lt_sixteen
      hns hN hrank S hnonab hZ E hE hunique hnormal hwidth A D hA hD hn hc hg)

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
