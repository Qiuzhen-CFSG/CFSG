module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Transfer

/-!
# The exceptional normalizer in Bender's odd-prime argument

This record spells out the exceptional configuration described on printed
p.225 of Bender, *Finite groups with large subgroups* (1974), proof of
(4.1): an elementary abelian group `A` of order 27, with
`N_G(A) = A V X`, where `V` is a four-group normalized by the group `X`
of order three. Normalization by `X` makes `V ⊔ X` the actual product;
normality of `A` in its normalizer then makes the outer supremum the
actual product as well.

The structural-alternatives proof must produce this record if the odd
complement is not cyclic of order `p` or 15. The exclusion proof may
assume the record and must derive a contradiction from the original
J₁ local hypotheses. Neither obligation is asserted by this definition.
-/

namespace CFSG.Quasithin.Janko1CentralizerData

variable {G : Type*} [Group G] [Finite G]

/-- The precise exceptional order-27 normalizer shape in Bender (4.1).
All normalizers and suprema are taken in the ambient group `G`. -/
public structure ExceptionalOddNormalizer (A : Subgroup G) : Prop where
  elementary : IsElementaryAbelian 3 A
  card : Nat.card A = 27
  normalizer_decomposition : ∃ V X : Subgroup G,
    IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧ Nat.card X = 3 ∧
      X ≤ Subgroup.normalizer (V : Set G) ∧
      Subgroup.normalizer (A : Set G) = A ⊔ (V ⊔ X)

/-- An exceptional odd complement can occur only at the prime three. -/
public theorem OddCentralizerComplement.prime_eq_three_of_exceptional
    {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A) (e : ExceptionalOddNormalizer A)
    (p : ℕ) (hp : p = 3 ∨ p = 5) (hx : orderOf x = p) : p = 3 := by
  have hxA : orderOf (⟨x, a.x_mem⟩ : A) = p :=
    (orderOf_injective A.subtype Subtype.val_injective ⟨x, a.x_mem⟩).symm.trans hx
  have hd := orderOf_dvd_natCard (⟨x, a.x_mem⟩ : A)
  rw [hxA, e.card] at hd
  rcases hp with rfl | rfl
  · rfl
  · norm_num at hd

end CFSG.Quasithin.Janko1CentralizerData
