module
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Cardinalities of fixed subgroups across equivariant surjections

An equivariant surjection between finite odd-order groups makes the cardinality
of the fixed subgroup of an involution, and of the common fixed subgroup of two
commuting involutions, a product of its image and kernel cardinalities. These
are the multiplicative steps used in central induction for the Brauer--Wielandt
formula (Gorenstein--Walter, Section 2, Lemma 3).

Fixed preimages exist by unique fixed/inverted factorization. The remaining
identity is the kernel/range cardinality formula for the restricted homomorphism.
-/

namespace MulAut
variable {G H : Type*} [Group G] [Group H]
private theorem card_subgroup_eq_card_map_mul_card_inf [Finite G]
    (f : G →* H) (K : Subgroup G) :
    Nat.card K = Nat.card (K.map f) * Nat.card ↥(f.ker ⊓ K) := by
  let φ := f.comp K.subtype
  have hr : φ.range = K.map f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  let e : φ.ker ≃ (f.ker ⊓ K : Subgroup G) :=
    { toFun := fun x => ⟨x.1.1, x.2, x.1.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    Nat.card K = Nat.card φ.range * Nat.card φ.ker := by
      rw [← Subgroup.index_ker, Subgroup.index_mul_card]
    _ = Nat.card (K.map f) * Nat.card ↥(f.ker ⊓ K) := by
      rw [hr, Nat.card_congr e]

public theorem fixedSubgroup_card_eq_quotient_mul_kernel [Finite G] [Finite H]
    (hG : Odd (Nat.card G)) (hH : Odd (Nat.card H))
    (a : MulAut G) (c : MulAut H) (ha : Function.Involutive a)
    (hc : Function.Involutive c) (f : G →* H) (hf : Function.Surjective f)
    (hac : ∀ x, f (a x) = c (f x)) :
    Nat.card (fixedSubgroup a) =
      Nat.card (fixedSubgroup c) * Nat.card ↥(f.ker ⊓ fixedSubgroup a) := by
  have hm : (fixedSubgroup a).map f = fixedSubgroup c := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      apply (mem_fixedSubgroup c (f x)).mpr
      rw [← hac, (mem_fixedSubgroup a x).mp hx]
    · intro hy
      obtain ⟨x, hx, hfx⟩ := exists_fixed_preimage_of_odd_card hG hH a c ha hc f hf hac y ((mem_fixedSubgroup c y).mp hy)
      exact ⟨x, (mem_fixedSubgroup a x).mpr hx, hfx⟩
  rw [card_subgroup_eq_card_map_mul_card_inf f, hm]

public theorem common_fixedSubgroup_card_eq_quotient_mul_kernel [Finite G] [Finite H]
    (hG : Odd (Nat.card G)) (hH : Odd (Nat.card H))
    (a b : MulAut G) (c d : MulAut H)
    (ha : Function.Involutive a) (hb : Function.Involutive b)
    (hc : Function.Involutive c) (hd : Function.Involutive d)
    (hab : Commute a b) (f : G →* H) (hf : Function.Surjective f)
    (hac : ∀ x, f (a x) = c (f x)) (hbd : ∀ x, f (b x) = d (f x)) :
    Nat.card ↥(fixedSubgroup a ⊓ fixedSubgroup b) =
      Nat.card ↥(fixedSubgroup c ⊓ fixedSubgroup d) *
        Nat.card ↥(f.ker ⊓ (fixedSubgroup a ⊓ fixedSubgroup b)) := by
  have hm : (fixedSubgroup a ⊓ fixedSubgroup b).map f =
      fixedSubgroup c ⊓ fixedSubgroup d := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      constructor
      · apply (mem_fixedSubgroup c (f x)).mpr
        rw [← hac, (mem_fixedSubgroup a x).mp hx.1]
      · apply (mem_fixedSubgroup d (f x)).mpr
        rw [← hbd, (mem_fixedSubgroup b x).mp hx.2]
    · intro hy
      obtain ⟨x, hax, hbx, hfx⟩ := exists_common_fixed_preimage_of_odd_card hG hH
        a b c d ha hb hc hd hab f hf hac hbd y ((mem_fixedSubgroup c y).mp hy.1) ((mem_fixedSubgroup d y).mp hy.2)
      exact ⟨x, ⟨(mem_fixedSubgroup a x).mpr hax, (mem_fixedSubgroup b x).mpr hbx⟩, hfx⟩
  rw [card_subgroup_eq_card_map_mul_card_inf f, hm]
end MulAut
