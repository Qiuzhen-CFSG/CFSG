module

public import Theory.FieldTheory.ScalarTwistedFixedPoints
import Mathlib.Tactic.LinearCombination

/-!
# Fixed points of triangular semilinear maps

For a nonidentity automorphism σ of a finite field F, choose an element t
outside its fixed field K. The map (a,b) ↦ a + tb embeds K² in F. Translation
by one solution reduces an affine scalar-twisted equation to the homogeneous
one, whose solution set has at most |K| elements. Counting the fibers over
the first coordinate then bounds a triangular two-coordinate fixed set by
|K|² ≤ |F|. The automorphism may have arbitrary order.

The PSL₃ large-actor fixer calculation consumes this bound on both root
planes, including the fields of orders two and four. Source application:
Aschbacher–Smith, E.1.14(1), printed p.214, via the standard semilinear
coordinates of GLS3 §2.5 and §2.7.
-/

public section

namespace FiniteField
variable {F : Type*} [Field F] [Finite F]

/-- Any proper automorphism fixed field has at most square-root order. -/
theorem card_fixed_sq_le (σ : F ≃+* F) (hne : σ ≠ 1) :
    Nat.card (FixedBy.subfield F σ) ^ 2 ≤ Nat.card F := by
  classical
  have ht : ∃ t : F, σ t ≠ t := by
    by_contra! h
    exact hne (RingEquiv.ext h)
  obtain ⟨t, ht⟩ := ht
  let K := FixedBy.subfield F σ
  let j : K × K → F := fun p => (p.1 : F) + t * (p.2 : F)
  have hj : Function.Injective j := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    change (a : F) + t * (b : F) = (c : F) + t * (d : F) at h
    have hs := congrArg σ h
    have ha : σ (a : F) = a := a.property
    have hb : σ (b : F) = b := b.property
    have hc : σ (c : F) = c := c.property
    have hd : σ (d : F) = d := d.property
    simp only [map_add, map_mul, ha, hb, hc, hd] at hs
    have he : (σ t - t) * ((b : F) - (d : F)) = 0 := by
      linear_combination hs - h
    have hbd : (b : F) = d := sub_eq_zero.mp
      ((mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr ht))
    have hac : (a : F) = c := by linear_combination h - t * hbd
    exact Prod.ext (Subtype.ext hac) (Subtype.ext hbd)
  simpa only [Nat.card_prod, pow_two] using Nat.card_le_card_of_injective j hj

/-- An affine scalar-twisted equation has at most one fixed-field coset of solutions. -/
theorem card_affine_scalar_fixed_le (σ : F ≃+* F) (c d : F) :
    Nat.card {x : F // c * σ x + d = x} ≤ Nat.card (FixedBy.subfield F σ) := by
  classical
  let S := {x : F // c * σ x + d = x}
  by_cases h : Nonempty S
  · obtain ⟨w⟩ := h
    let j : S → {x : F // c * σ x = x} := fun x => ⟨x.val - w.val, by
      rw [map_sub, mul_sub]
      linear_combination x.property - w.property⟩
    exact (Nat.card_le_card_of_injective j (by
      intro x y hxy
      apply Subtype.ext
      exact sub_left_injective (congrArg Subtype.val hxy))).trans
        (card_scalar_fixed_le σ c)
  · have : IsEmpty S := not_nonempty_iff.mp h
    have hz : Nat.card S = 0 := by simp
    exact hz ▸ Nat.zero_le _

/-- Triangular semilinear equations in two coordinates have at most |F| solutions
when the coefficient automorphism is nontrivial. The off-diagonal term can be
any function of the first coordinate. -/
theorem card_triangular_fixed_le (σ : F ≃+* F) (hne : σ ≠ 1)
    (a b : F) (t : F → F) :
    Nat.card {p : F × F // a * σ p.1 = p.1 ∧ b * σ p.2 + t p.1 = p.2} ≤
      Nat.card F := by
  classical
  let X := {x : F // a * σ x = x}
  let Y := fun x : X => {z : F // b * σ z + t x.val = z}
  let S := {p : F × F // a * σ p.1 = p.1 ∧ b * σ p.2 + t p.1 = p.2}
  let j : S → Sigma Y := fun p => ⟨⟨p.val.1,p.property.1⟩,⟨p.val.2,p.property.2⟩⟩
  have hj : Function.Injective j := by
    intro p q h
    have hx := congrArg (fun s : Sigma Y => s.1.val) h
    have hy := congrArg (fun s : Sigma Y => s.2.val) h
    exact Subtype.ext (Prod.ext hx hy)
  let : Fintype X := Fintype.ofFinite X
  calc
    Nat.card S ≤ Nat.card (Sigma Y) := Nat.card_le_card_of_injective j hj
    _ = ∑ x : X, Nat.card (Y x) := Nat.card_sigma
    _ ≤ ∑ _x : X, Nat.card (FixedBy.subfield F σ) :=
      Finset.sum_le_sum (fun x _ => card_affine_scalar_fixed_le σ b (t x.val))
    _ = Nat.card X * Nat.card (FixedBy.subfield F σ) := by
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_eq_nat_card]
    _ ≤ Nat.card (FixedBy.subfield F σ) ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul_right _ (card_scalar_fixed_le σ a)
    _ ≤ Nat.card F := card_fixed_sq_le σ hne
end FiniteField
