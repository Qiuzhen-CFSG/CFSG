module

public import Stellmacher.Recognition.LyonsU3Four.Normalizer
public import Stellmacher.Recognition.LyonsU3Four.NTwoInvolutionCentralizer
public import Stellmacher.Recognition.LyonsU3Four.OrderFourFusionFromAutomizer

/-!
# Local inputs for the N2 Lyons assembly

The character calculation and the coprime-action index argument can proceed
independently from the same explicit local data. The supplied Sylow subgroup
has automizer fifteen. Each central involution centralizer factors as its
actual odd core times its Sylow normalizer; its actual odd-core quotient is
an order-five semidirect extension preserving the supplied Sylow embedding.
Order-four centralizers have odd-core quotient of order sixteen.

The N2 hypothesis proves these data using solvability of involution
centralizers. No assertion about the ambient character table or triviality
of local odd cores is included in this interface.
Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 1,
pp. 372–373, specialized using two-local solvability.
-/

namespace Stellmacher.Recognition.LyonsU3Four

open Subgroup

/-- The exact local inputs consumed independently by the ambient character
calculation and the fourth-power action-index argument. -/
public structure LocalCentralizerData {G : Type*} [Group G] (S : Sylow 2 G) : Prop where
  automizer_fifteen : automizerIndex S = 15
  involution_factorization : ∀ (z : G) (hz : z ∈ centerImage S), z ≠ 1 →
    ∀ c : centralizer ({z} : Set G),
      ∃ o ∈ pPrimeCore 2 (centralizer ({z} : Set G)),
        ∃ n ∈ normalizer (centralizerSylow S hz : Set (centralizer ({z} : Set G))),
          o * n = c
  involution_quotient : ∀ (z : G) (hz : z ∈ centerImage S), z ≠ 1 →
    ∃ (β : MulAut S) (α : Multiplicative (ZMod 5) →* MulAut S),
      orderOf β = 5 ∧ α (Multiplicative.ofAdd (1 : ZMod 5)) = β ∧
      ∃ e : (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) ≃*
        S ⋊[α] Multiplicative (ZMod 5),
        ∀ s : S, e (involutionCentralizerQuotientMap S hz s) = SemidirectProduct.inl s
  orderFour_quotient_card : ∀ t : S, orderOf t = 4 →
    Nat.card (centralizer ({(t : G)} : Set G) ⧸
      pPrimeCore 2 (centralizer ({(t : G)} : Set G))) = 16

/-- The actual N2 hypothesis discharges every local input, including the
Sylow automizer order and the order-four centralizer cardinality. -/
public theorem localCentralizerData_of_isNTwoGroup
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (h : SylowStructure S) :
    LocalCentralizerData S := by
  have h15 := automizerIndex_eq_fifteen S h
  refine ⟨h15, ?_, ?_, ?_⟩
  · intro z hz hz1 c
    exact involutionCentralizer_factorization_of_isNTwoGroup hN S h hz hz1 c
  · intro z hz hz1
    exact exists_orderFive_involutionCentralizer_equiv_of_isNTwoGroup hN S h h15 hz hz1
  · intro t ht
    exact orderFour_centralizer_quotient_card_of_isNTwoGroup hN S h h15 t ht
      (order_four_centralizer_card_of_automizer_eq_fifteen S h h15 t ht)

end Stellmacher.Recognition.LyonsU3Four
