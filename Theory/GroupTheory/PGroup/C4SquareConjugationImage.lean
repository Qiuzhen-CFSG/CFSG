module

public import Theory.GroupTheory.PGroup.C4SquareIndexEight

/-!
# The congruence kernel in a C₄-square conjugation image

If an elementary subgroup and an abelian base generate the centralizer of
the omega four, the elementary subgroup induces exactly those ambient
automorphisms which fix every element of square one. This identifies the
actual subgroup to which a finite automorphism calculation must be applied.

The proof maps the centralizer product through conjugation: the abelian base
has trivial image. Fixing the omega four is equivalent to fixing its elements
of square one, since the omega four is elementary.

Source context: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3(a), p.386.
-/

open Subgroup
namespace C4SquareExtension

/-- The elementary image is precisely the subgroup fixing the omega four. -/
public theorem mem_elementary_conj_image_iff_fix_square_one
    {P : Type*} [Group P] (W D B : Subgroup P)
    [D.Normal] [IsMulCommutative D]
    [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 B]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W) (hWB : W ≤ B)
    (hC : centralizer (W : Set P) = B ⊔ D)
    (α : MulAut D) (hα : α ∈ (MulAut.conjNormal : P →* MulAut D).range) :
    α ∈ ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ↔
      ∀ d : D, d ^ 2 = 1 → α d = d := by
  let f : P →* MulAut D := MulAut.conjNormal
  have hWD : W ≤ D := hO ▸ map_subtype_le _
  have hmap : (centralizer (W : Set P)).map f = B.map f := by
    have hD : D.map f = ⊥ := (Subgroup.map_eq_bot_iff D).mpr (by
      rw [conjNormal_ker_eq_of_selfCentralizing_abelian D hDC])
    rw [hC, Subgroup.map_sup, hD, sup_bot_eq]
  constructor
  · rintro ⟨b, rfl⟩ d hd
    have hdW : (d : P) ∈ W := by
      rw [← hO]
      refine ⟨d, subset_closure ?_, rfl⟩
      simpa using hd
    apply Subtype.ext
    change (b : P) * (d : P) * (b : P)⁻¹ = d
    rw [(B.le_centralizer b.property d (hWB hdW)).symm, mul_inv_cancel_right]
  · intro hfix
    obtain ⟨g, rfl⟩ := hα
    have hg : g ∈ centralizer (W : Set P) := by
      intro w hw
      have hw2 : (⟨w, hWD hw⟩ : D) ^ 2 = 1 := by
        apply Subtype.ext
        exact elemPow_eq_one_of_isElementaryAbelian w hw
      have hh := congrArg (fun d : D => (d : P)) (hfix ⟨w, hWD hw⟩ hw2)
      change g * w * g⁻¹ = w at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    change f g ∈ (f.comp B.subtype).range
    rw [MonoidHom.range_comp, range_subtype, ← hmap]
    exact mem_map_of_mem f hg

end C4SquareExtension
