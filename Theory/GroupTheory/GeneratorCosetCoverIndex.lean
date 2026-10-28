module

public import Theory.GroupTheory.PresentedGroupBounds
public import Mathlib.GroupTheory.Index

/-!
# Index bounds from generator coset certificates

A generator coset cover supplies an upper bound on a subgroup's index, without
requiring the order of the subgroup. A family of distinct right cosets supplies
the reverse bound. The two families may be constructed independently.

The cover uses right cosets `H * r`. Sending `r` to the left coset of `r⁻¹`
matches Mathlib's quotient convention. Word induction in `GeneratorCosetCover.covers`
proves surjectivity; coset separation proves injectivity. This is the usual
covering and separation argument underlying certified Todd–Coxeter enumeration
(Todd and Coxeter, Proc. Edinburgh Math. Soc. 5 (1936), 26–34).
-/

namespace Subgroup

/-- A finite generator coset cover bounds the index, even for an infinite subgroup. -/
public theorem GeneratorCosetCover.index_le_card {G α ι : Type*} [Group G]
    {H : Subgroup G} {g : α → G} [Finite ι]
    (C : GeneratorCosetCover H g ι) (hgen : closure (Set.range g) = ⊤) :
    H.index ≤ Nat.card ι := by
  let f : ι → G ⧸ H := fun i => QuotientGroup.mk ((C.repr i)⁻¹)
  have hf : Function.Surjective f := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      obtain ⟨h, i, hi⟩ := C.covers hgen x⁻¹
      refine ⟨i, Quotient.sound ?_⟩
      apply QuotientGroup.leftRel_apply.mpr
      have hx : x = (C.repr i)⁻¹ * h.val⁻¹ := by
        simpa only [inv_inv, mul_inv_rev] using congrArg Inv.inv hi
      simpa only [inv_inv, hx, mul_inv_cancel_left] using H.inv_mem h.property
  exact Nat.card_le_card_of_surjective f hf

/-- Distinct right cosets give a lower bound on a finite index. -/
public theorem card_le_index_of_rightCoset_separation {G ι : Type*} [Group G]
    (H : Subgroup G) [Finite (G ⧸ H)] (r : ι → G)
    (hsep : ∀ i j, r i * (r j)⁻¹ ∈ H → i = j) :
    Nat.card ι ≤ H.index := by
  let f : ι → G ⧸ H := fun i => QuotientGroup.mk ((r i)⁻¹)
  apply Nat.card_le_card_of_injective f
  intro i j hij
  apply hsep i j
  have h := QuotientGroup.leftRel_apply.mp (Quotient.exact hij)
  simpa only [inv_inv] using h

end Subgroup
