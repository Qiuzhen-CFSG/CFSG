module
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.GroupAction.KleinFourFactorInjective
public import Mathlib.Tactic.Ring

/-!
# Cardinality bounds from four Klein-four factors

For commuting involutive automorphisms a and b of a finite odd-order group,
the product of the orders of their three fixed subgroups equals the number
of tuples in the four-factor decomposition domain times the square of the
common fixed-subgroup order. Injectivity of four-factor multiplication then
bounds this product by |G| times that same square. Neither result assumes
solubility, faithfulness of the Klein-four action, or the Brauer--Wielandt
cardinality formula.

Unique fixed/inverted splitting under b, restricted to points fixed by a,
is a bijection from common fixed points times a-fixed/b-inverted points to
Fix(a). Commutation and uniqueness ensure both factors remain a-fixed.
Apply this to the three nonidentity positions of the Klein four and
multiply the resulting cardinal equalities. The inequality follows from
`MulAut.fixed_inverted_four_factor_injective`.

This follows Gorenstein--Walter, *On finite groups with dihedral Sylow
2-subgroups*, Section 2, Lemma 4(i--ii). The exact domain-cardinality identity
also supports the later three-fixed-subgroup factorization, once the
Brauer--Wielandt formula supplies equality in the bound.
-/

namespace MulAut
variable {G : Type*} [Group G] [Finite G]

private theorem fixed_card_split (odd : Odd (Nat.card G))
    (a b : MulAut G) (hb : Function.Involutive b) (hab : Commute a b) :
    Nat.card (fixedSubgroup a) =
      Nat.card {h : G // a h = h ∧ b h = h} *
        Nat.card {x : G // a x = x ∧ b x = x⁻¹} := by
  let m : {h : G // a h = h ∧ b h = h} × {x : G // a x = x ∧ b x = x⁻¹} →
      fixedSubgroup a := fun p => ⟨p.1.val * p.2.val,
        by simp [p.1.property.1,p.2.property.1]⟩
  have hm : Function.Bijective m := by
    constructor
    · rintro ⟨h,x⟩ ⟨h',x'⟩ heq
      obtain ⟨p,hp,huniq⟩ :=
        Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card odd b hb (h*x)
      have h1 := huniq (h,x) ⟨h.property.2,x.property.2,rfl⟩
      have h2 := huniq (h',x') ⟨h'.property.2,x'.property.2,
        (congrArg Subtype.val heq).symm⟩
      exact Prod.ext (Subtype.ext (congrArg Prod.fst (h1.trans h2.symm)))
        (Subtype.ext (congrArg Prod.snd (h1.trans h2.symm)))
    · intro x
      obtain ⟨⟨u,v⟩,⟨hu,hv,huv⟩,huniq⟩ :=
        Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card odd b hb x.val
      have hba (z : G) : b (a z) = a (b z) :=
        (congrArg (fun f : MulAut G => f z) hab.eq).symm
      have hx : a x.val = x.val := (mem_fixedSubgroup a x.val).mp x.property
      have heq := huniq (a u,a v)
        ⟨by rw [hba,hu],by rw [hba,hv,map_inv],by rw [← map_mul,huv,hx]⟩
      exact ⟨(⟨u,congrArg Prod.fst heq,hu⟩,⟨v,congrArg Prod.snd heq,hv⟩),
        Subtype.ext huv⟩
  exact (Nat.card_congr (Equiv.ofBijective m hm)).symm.trans (Nat.card_prod _ _)

/-- The three fixed-subgroup orders count the four-factor domain, with the
square of the common-fixed order as multiplicity. -/
public theorem fixedSubgroup_card_product_eq_four_factors_card_mul (odd : Odd (Nat.card G))
    (a b : MulAut G) (ha : Function.Involutive a) (hb : Function.Involutive b)
    (hab : Commute a b) :
    Nat.card (fixedSubgroup a) * Nat.card (fixedSubgroup b) *
      Nat.card (fixedSubgroup (a*b)) =
        Nat.card ({h : G // a h = h ∧ b h = h} ×
          {x : G // a x = x ∧ b x = x⁻¹} ×
          {y : G // a y = y⁻¹ ∧ b y = y} ×
          {z : G // a z = z⁻¹ ∧ b z = z⁻¹}) *
          Nat.card ↥(fixedSubgroup a ⊓ fixedSubgroup b)^2 := by
  let K := {h : G // a h = h ∧ b h = h}
  let X := {x : G // a x = x ∧ b x = x⁻¹}
  let Y := {y : G // a y = y⁻¹ ∧ b y = y}
  let Z := {z : G // a z = z⁻¹ ∧ b z = z⁻¹}
  have hK : Nat.card ↥(fixedSubgroup a ⊓ fixedSubgroup b) = Nat.card K := by
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => by simp))
  have hA : Nat.card (fixedSubgroup a) = Nat.card K * Nat.card X :=
    fixed_card_split odd a b hb hab
  have hB : Nat.card (fixedSubgroup b) = Nat.card K * Nat.card Y := by
    rw [fixed_card_split odd b a ha hab.symm]
    congr 1
    · exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => and_comm))
    · exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => and_comm))
  have hca : Commute (a*b) a := by
    apply DFunLike.ext
    intro t
    change a (b (a t)) = a (a (b t))
    exact congrArg a ((congrArg (fun f : MulAut G => f t) hab.eq).symm)
  have hC : Nat.card (fixedSubgroup (a*b)) = Nat.card K * Nat.card Z := by
    rw [fixed_card_split odd (a*b) a ha hca]
    congr 1
    · apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro x
      constructor
      · rintro ⟨hc,hax⟩
        refine ⟨hax, ?_⟩
        have he := congrArg a hc
        change a (a (b x)) = a x at he
        exact (ha _).symm.trans (he.trans hax)
      · rintro ⟨hax,hbx⟩
        exact ⟨by simp [MulAut.mul_apply,hax,hbx],hax⟩
    · apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro x
      constructor
      · rintro ⟨hc,hax⟩
        refine ⟨hax, ?_⟩
        have he := congrArg a hc
        change a (a (b x)) = a x at he
        exact (ha _).symm.trans (he.trans hax)
      · rintro ⟨hax,hbx⟩
        exact ⟨by simp [MulAut.mul_apply,hax,hbx],hax⟩
  rw [hA,hB,hC,hK]
  simp only [Nat.card_prod]
  change (Nat.card K * Nat.card X) * (Nat.card K * Nat.card Y) *
    (Nat.card K * Nat.card Z) =
    (Nat.card K * (Nat.card X * (Nat.card Y * Nat.card Z))) * Nat.card K^2
  ring

/-- Four-factor uniqueness bounds the product of the three fixed-subgroup orders. -/
public theorem fixedSubgroup_card_product_le (odd : Odd (Nat.card G))
    (a b : MulAut G) (ha : Function.Involutive a) (hb : Function.Involutive b)
    (hab : Commute a b) :
    Nat.card (fixedSubgroup a) * Nat.card (fixedSubgroup b) *
      Nat.card (fixedSubgroup (a*b)) ≤
        Nat.card G * Nat.card ↥(fixedSubgroup a ⊓ fixedSubgroup b)^2 := by
  rw [fixedSubgroup_card_product_eq_four_factors_card_mul odd a b ha hb hab]
  exact Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective _
    (fixed_inverted_four_factor_injective odd a b ha hb hab))
end MulAut
