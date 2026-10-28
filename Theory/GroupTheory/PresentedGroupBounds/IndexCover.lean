module

public import Theory.GroupTheory.PresentedGroupBounds
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Fintype.EquivFin

/-!
# Generator coset covers from finite index bounds

Choose a section of the usual left-coset quotient, normalized at the identity
class. Inverting this section yields right-coset representatives. An embedding
of the quotient into `Fin n` then gives actual subgroup-witness transitions for
any marked generators whenever the index is at most n. This is the elementary
coset-section argument; the subgroup need not be normal.

The M24 max8 application is in `NativeActions.OrderBound.CosetCover`.
-/

@[expose] public section
namespace Subgroup

/-- An index bound supplies representatives with actual subgroup multipliers.
The representatives invert a section of the usual left-coset quotient, so
that the multiplier in every transition is on the left. -/
noncomputable def GeneratorCosetCover.of_index_le {G α : Type*} [Group G] [Finite G]
    (H : Subgroup G) (g : α → G) (n : ℕ) (hindex : H.index ≤ n) :
    GeneratorCosetCover H g (Fin n) := by
  classical
  let Q := G ⧸ H
  letI : Fintype Q := Fintype.ofFinite Q
  have hc : Fintype.card Q ≤ Fintype.card (Fin n) := by
    simpa only [Fintype.card_eq_nat_card, Nat.card_fin, Subgroup.index_eq_card] using hindex
  let e : Q ↪ Fin n := Classical.choice (Function.Embedding.nonempty_of_card_le hc)
  let q : Fin n → Q := Function.invFun e
  have hq (j : Q) : q (e j) = j := Function.leftInverse_invFun e.injective j
  let q0 : Q := QuotientGroup.mk (1 : G)
  let r : Q → G := fun j => if j = q0 then 1 else (Quotient.out j)⁻¹
  have hr (j : Q) : QuotientGroup.mk ((r j)⁻¹) = j := by
    dsimp only [r]
    split_ifs with h
    · simpa only [inv_one] using h.symm
    · simpa only [inv_inv] using Quotient.out_eq j
  have hx (x : G) : ∃ h : H, ∃ i : Fin n, x = h.val * r (q i) := by
    let j : Q := QuotientGroup.mk x⁻¹
    have he : x * (r j)⁻¹ ∈ H := by
      have he := QuotientGroup.eq.mp (hr j).symm
      simpa only [inv_inv] using he
    refine ⟨⟨x * (r j)⁻¹, he⟩, e j, ?_⟩
    rw [hq]
    simp only [inv_mul_cancel_right]
  exact {
    repr := fun i => r (q i)
    initial := e q0
    initial_eq := by rw [hq]; exact if_pos rfl
    step := fun i a => hx (r (q i) * g a)
    inv_step := fun i a => hx (r (q i) * (g a)⁻¹)
  }

end Subgroup
