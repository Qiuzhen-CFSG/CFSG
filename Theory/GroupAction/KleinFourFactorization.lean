module
public import Theory.GroupAction.KleinFourCardinality

/-!
# Three fixed subgroups factor an odd group with a Klein-four action

Let a and b be commuting involutive automorphisms of a finite odd-order
group G. Every element is a product, in order, of a point fixed by a, a point
fixed by b, and a point fixed by ab. The stronger four-factor bijection also
records the common-fixed factor and the three fixed/inverted factors.
No solubility or faithfulness assumption is imposed on the action.

The multiplication map on the four-factor domain is already injective.
Its exact cardinality identity, together with the Brauer--Wielandt formula,
makes the domain equicardinal with G after cancelling the positive square
of the common fixed-subgroup order. Hence the map is bijective. Absorbing
the common-fixed factor into the first factor gives the stated three-factor
product; a point inverted by both automorphisms is fixed by their product.

This is Gorenstein--Walter, *On finite groups with dihedral Sylow 2-subgroups*,
Section 2, Lemma 4(ii), and the three-fixed-subgroup formula quoted in Brauer,
*On finite Desarguesian planes II*, (6E), equation (6.4), article page 135.
It supplies the odd-group factorization used by the ABG local action analysis.
-/

namespace MulAut
variable {G : Type*} [Group G] [Finite G]

/-- The common-fixed and three fixed/inverted factors give unique coordinates. -/
public theorem fixed_inverted_four_factor_bijective (odd : Odd (Nat.card G))
    (a b : MulAut G) (ha : Function.Involutive a) (hb : Function.Involutive b)
    (hab : Commute a b) :
    Function.Bijective (fun p :
      {h : G // a h = h ∧ b h = h} ×
      {x : G // a x = x ∧ b x = x⁻¹} ×
      {y : G // a y = y⁻¹ ∧ b y = y} ×
      {z : G // a z = z⁻¹ ∧ b z = z⁻¹} =>
      p.1.val * p.2.1.val * p.2.2.1.val * p.2.2.2.val) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨fixed_inverted_four_factor_injective odd a b ha hb hab, ?_⟩
  have hcard := Theory.GroupAction.brauerWielandt_fixedSubgroup_card odd a b ha hb hab
  have h := (fixedSubgroup_card_product_eq_four_factors_card_mul odd a b ha hb hab).symm.trans hcard.symm
  exact Nat.mul_right_cancel (pow_pos (Nat.card_pos) 2) h

/-- An odd group is the ordered set product of the three involution-fixed subgroups. -/
public theorem exists_fixed_mul_fixed_mul_fixed_of_odd_card (odd : Odd (Nat.card G))
    (a b : MulAut G) (ha : Function.Involutive a) (hb : Function.Involutive b)
    (hab : Commute a b) (x : G) : ∃ x₀ x₁ x₂ : G,
      a x₀ = x₀ ∧ b x₁ = x₁ ∧ (a*b) x₂ = x₂ ∧ x = x₀*x₁*x₂ := by
  obtain ⟨⟨h,u,v,w⟩,hp⟩ :=
    (fixed_inverted_four_factor_bijective odd a b ha hb hab).surjective x
  refine ⟨h*u,v,w,?_,v.property.2,?_,hp.symm⟩
  · simp only [map_mul,h.property.1,u.property.1]
  · simp [MulAut.mul_apply,w.property.1,w.property.2]
end MulAut
