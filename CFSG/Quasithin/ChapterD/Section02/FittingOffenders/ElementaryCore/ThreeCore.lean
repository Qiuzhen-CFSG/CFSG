module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.ElementaryCore
public import Theory.PGroupCore

/-!
# Application to the actual three-core

Specialize the elementary-core argument to `O₃(G)`. Its normality supplies
the normalization hypothesis and its defining three-group property supplies
the prime-power input. The result includes trivial Frattini subgroup,
elementarity, the actual product equivalence and the full commutator.
The hyperplane-support premises remain exactly the earlier-source input
owned by `qt-d-02-fitting-offenders`.

Source: Aschbacher--Smith, D.2.14(2), printed p.186.
-/

public section
namespace CFSG.Quasithin.ChapterD.ElementaryCore
open Subgroup Representation.BinaryOffender

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Order and full-commutator conclusions for the source's actual `O₃(G)`. -/
theorem threeCore_order_and_commutator (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4)
    (hf : A ⊓ centralizer (pCore 3 G : Set G) = ⊥)
    (hfix : pCore 3 G ⊓ centralizer (A : Set G) = ⊥)
    (hs : HyperplaneSupport ρ (pCore 3 G) A) :
    (∃ s : ℕ, (s = 2 ∨ s = 3) ∧ Nat.card (pCore 3 G) = 3 ^ s) ∧
      ⁅pCore 3 G, A⁆ = pCore 3 G := by
  exact order_and_commutator_of_hyperplaneSupport ρ (pCore 3 G) A pCore_isPGroup hA
    (by rw [normalizer_eq_top]; exact le_top) hf hfix hs

/-- The support input on `O₃(G)` restricts to each invariant order-three
subgroup without changing either centralizer convention. -/
theorem threeCore_line_fixed_support (A Z : Subgroup G) (hA : Nat.card A = 4)
    (hZP : Z ≤ pCore 3 G) (hZ : Nat.card Z = 3)
    (hnZ : A ≤ normalizer (Z : Set G))
    (hfix : pCore 3 G ⊓ centralizer (A : Set G) = ⊥)
    (hs : HyperplaneSupport ρ (pCore 3 G) A) :
    let B := A ⊓ centralizer (Z : Set G)
    Nat.card B = 2 ∧ rank B = 1 ∧ pCore 3 G ⊓ centralizer (B : Set G) = Z ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ (fixedSpace ρ B) Z) = 2 :=
  line_fixed_support ρ (pCore 3 G) A Z hA hZP hZ hnZ hfix hs

variable [FiniteDimensional (ZMod 2) V]

/-- The source's actual three-core is elementary abelian, by the proved
support exclusion and invariant central-line detection. -/
theorem threeCore_frattini_and_elementary (hρ : Function.Injective ρ)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 4)
    (hfix : pCore 3 G ⊓ centralizer (A : Set G) = ⊥)
    (hs : HyperplaneSupport ρ (pCore 3 G) A) :
    frattini (pCore 3 G) = ⊥ ∧ IsElementaryAbelian 3 (pCore 3 G) := by
  exact frattini_eq_bot_and_isElementaryAbelian_of_hyperplaneSupport
    ρ hρ (pCore 3 G) A pCore_isPGroup hA
    (by rw [normalizer_eq_top]; exact le_top) hfix hs

/-- D.2.14(2)'s elementary-core conclusion for the literal `O₃(G)`,
conditional precisely on the preceding hyperplane and action conclusions. -/
theorem threeCore_elementary_structure (hρ : Function.Injective ρ)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 4)
    (hf : A ⊓ centralizer (pCore 3 G : Set G) = ⊥)
    (hfix : pCore 3 G ⊓ centralizer (A : Set G) = ⊥)
    (hs : HyperplaneSupport ρ (pCore 3 G) A) :
    IsElementaryAbelian 3 (pCore 3 G) ∧
      (∃ s : ℕ, (s = 2 ∨ s = 3) ∧ Nat.card (pCore 3 G) = 3 ^ s ∧
        Nonempty ((pCore 3 G) ≃* (Fin s → Multiplicative (ZMod 3)))) ∧
      ⁅pCore 3 G, A⁆ = pCore 3 G := by
  exact elementary_structure_of_hyperplaneSupport ρ hρ (pCore 3 G) A pCore_isPGroup hA
    (by rw [normalizer_eq_top]; exact le_top) hf hfix hs

end CFSG.Quasithin.ChapterD.ElementaryCore
