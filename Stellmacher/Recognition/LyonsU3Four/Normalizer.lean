module

public import Stellmacher.Recognition.LyonsU3Four.InvolutionFusion
public import Stellmacher.Recognition.LyonsU3Four.NormalizerAction
public import Stellmacher.Recognition.LyonsU3Four.AutomizerCalculation
public import Stellmacher.Recognition.LyonsU3Four.OrderThreeExclusion

/-!
# Lyons's Sylow normalizer

For a finite simple group with the intrinsic Sylow structure of Lyons's
Theorem 2, all involutions are conjugate and the Sylow normalizer modulo
its odd core is the semidirect product of the supplied Sylow subgroup by
a cyclic group of order fifteen.

The automizer calculation excludes factors seven and nine, leaving orders
three and fifteen. The order-three exclusion uses normal complements in
involution centralizers and Glauberman's Suzuki characterization. This
leaves order fifteen, so the conditional splitting and action theorems
apply. The equivalence preserves the canonical embedding of the supplied
Sylow subgroup. Its complement generator fixes only the identity, acts
transitively on the nonidentity central cosets, and induces an order-three
action on the center. Fixed-point-freeness is asserted for the generator;
its cube fixes the center.

Involution fusion is re-exported as `involutions_isConj`.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 1,
printed pp. 372–373.
-/

namespace Stellmacher.Recognition.LyonsU3Four

/-- The actual Sylow automizer has order fifteen. -/
public theorem automizerIndex_eq_fifteen
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) : automizerIndex S = 15 :=
  (automizerIndex_eq_three_or_fifteen S h).resolve_left (automizerIndex_ne_three S h)

/-- Lyons's Sylow-normalizer structure under exactly the intrinsic Sylow
hypothesis. The same order-fifteen automorphism supplies the action properties
and the semidirect product, with compatibility on the supplied Sylow subgroup. -/
public theorem exists_sylowNormalizer_structure
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) :
    ∃ (β : MulAut S) (α : Multiplicative (ZMod 15) →* MulAut S),
      orderOf β = 15 ∧
      α (Multiplicative.ofAdd (1 : ZMod 15)) = β ∧
      (∀ s : S, β s = s → s = 1) ∧
      (∀ x y : S ⧸ Subgroup.center S, x ≠ 1 → y ≠ 1 →
        ∃ n : ℤ, (Subgroup.quotientAut (Subgroup.center S) β ^ n) x = y) ∧
      orderOf (MulAut.characteristic (Subgroup.center S) β) = 3 ∧
      (∀ x y : Subgroup.center S, x ≠ 1 → y ≠ 1 →
        ∃ n : ℤ, (MulAut.characteristic (Subgroup.center S) β ^ n) x = y) ∧
      ∃ e : (Subgroup.normalizer (S : Set G) ⧸
          pPrimeCore 2 (Subgroup.normalizer (S : Set G))) ≃*
          S ⋊[α] Multiplicative (ZMod 15),
        ∀ s : S, e (sylowNormalizerQuotientMap S s) = SemidirectProduct.inl s :=
  exists_orderFifteen_normalizer_structure S h (automizerIndex_eq_fifteen S h)

end Stellmacher.Recognition.LyonsU3Four
