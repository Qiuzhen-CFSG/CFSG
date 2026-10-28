module

public import Stellmacher.Recognition.NormalFourNonnormalCoreSetup
public import Stellmacher.Recognition.NormalFourNonnormalCoreBounds
public import Stellmacher.Recognition.NormalFourNonnormalTerminalFusion
public import Theory.SpecificGroups.AffineEight.ElementaryEight

/-!
# Order and fusion assembly for the nonnormal quotient-image branch

The actual quotient is `N_G(Ω₁(Z(S)))/O₂′`. A two-core of order 16 and
relative index two in the quotient Sylow give `|S| = 32`. The faithful
split cyclic-eight/four model is excluded even inside this quotient:
its elementary eight violates the rank bound, which lifts through the
odd kernel.

The final assembly uses the ambient core order/index calculation and the
terminal fusion theorem to discharge all intermediate premises. The latter
excludes the outside-core case directly by the elementary rank bound. The
conditional fusion-or-affine assembly remains available; its affine alternative
requires an actual group isomorphism.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, pp.389–393.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The actual quotient core of order sixteen and Sylow relative index two
force the original Sylow subgroup to have order thirty-two. -/
public theorem card_sylow_eq_thirty_two_of_core_order_index (S : Sylow 2 G)
    (hcore : Nat.card (pCore 2 (OmegaQuotient S)) = 16)
    (hindex : (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) = 2) :
    Nat.card S = 32 := by
  have hle : pCore 2 (OmegaQuotient S) ≤ omegaQuotientSylow S :=
    pCore_isPGroup.le_sylow_of_normal _
  have hcard := ((pCore 2 (OmegaQuotient S)).subgroupOf
    (omegaQuotientSylow S)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at hcard
  change Nat.card (pCore 2 (OmegaQuotient S)) *
    (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) =
      Nat.card (omegaQuotientSylow S) at hcard
  rw [hcore, hindex] at hcard
  exact (Nat.card_congr (omegaQuotientSylowEquiv S).toEquiv).trans hcard.symm

/-- The terminal faithful split model cannot embed even in the actual odd-core
quotient, because its elementary eight lifts to the original ambient group. -/
public theorem not_injective_affineEight_into_omegaQuotient
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (f : AffineEight.Model →* OmegaQuotient S) :
    ¬ Function.Injective f := by
  apply AffineEight.not_injective_of_elementary_card_lt_eight _ f
  intro A hA
  let : IsElementaryAbelian 2 A := hA
  exact omegaQuotient_rank hrank S A

/-- Assemble order and fusion from the two remaining ambient inputs. The
alternative split model is eliminated in the actual quotient. -/
public theorem order_and_fusion_of_core_order_index_and_alternatives
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (E : Subgroup S)
    (hcore : Nat.card (pCore 2 (OmegaQuotient S)) = 16)
    (hindex : (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) = 2)
    (hterminal : (∀ x y : E, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G)) ∨
      Nonempty (S ≃* AffineEight.Model)) :
    Nat.card S = 32 ∧
      ∀ x y : E, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G) := by
  refine ⟨card_sylow_eq_thirty_two_of_core_order_index S hcore hindex, ?_⟩
  rcases hterminal with hfused | ha
  · exact hfused
  · obtain ⟨e⟩ := ha
    exact (not_injective_affineEight_into_omegaQuotient hrank S
      ((omegaQuotientHom S).comp e.symm.toMonoidHom)
      ((omegaQuotientHom_injective S).comp e.symm.injective)).elim

/-- The order-and-fusion conclusion of Janko–Thompson Lemma 4.1 when the
unique normal four has nonnormal image in `N_G(Ω₁(Z(S)))/O₂′`. -/
public theorem order_and_fusion_of_fourImage_not_normal
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal) :
    Nat.card S = 32 ∧
      ∀ x y : E, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G) := by
  obtain ⟨hcore, hindex⟩ :=
    omegaQuotient_pCore_order_index hns hN hrank S hnonab hZ E hE hunique hnormal
  exact ⟨card_sylow_eq_thirty_two_of_core_order_index S hcore hindex,
    terminal_fusion_of_core_order_index hns hN hrank S hZ E hE hunique hnormal
      hcore hindex⟩

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
