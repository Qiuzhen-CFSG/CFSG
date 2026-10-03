module
public import Theory.GroupTheory.FixedInvertedFactorization
public import Mathlib.GroupTheory.Index

/-!
# Fixed subgroups of automorphisms and odd-order lifting

The fixed subgroup of an automorphism is its equalizer with the identity.
For equivariant surjections of finite odd-order groups, fixed points of one
involution, or of two commuting involutions, have fixed preimages. These are
the quotient-transfer steps in the Brauer--Wielandt cardinality formula.

The proof uses the unique fixed/inverted factorization proved in
`Theory.GroupTheory.FixedInvertedFactorization`, following the
Gorenstein--Herstein argument cited in Gorenstein--Walter, Section 2,
Lemma 4(i). The image of the factorization of a lift agrees with `(y, 1)`.
For two involutions, first lift a point fixed by the first; uniqueness makes
its factorization under the second fixed by the first as well.
-/

namespace MulAut
variable {G H : Type*} [Group G] [Group H]
public def fixedSubgroup (a : MulAut G) : Subgroup G :=
  a.toMonoidHom.eqLocus (MonoidHom.id G)
@[simp] public theorem mem_fixedSubgroup (a : MulAut G) (x : G) :
    x ∈ fixedSubgroup a ↔ a x = x := Iff.rfl

public theorem exists_fixed_preimage_of_odd_card [Finite G] [Finite H]
    (hG : Odd (Nat.card G)) (hH : Odd (Nat.card H))
    (a : MulAut G) (b : MulAut H) (ha : Function.Involutive a)
    (hb : Function.Involutive b) (f : G →* H) (hf : Function.Surjective f)
    (heq : ∀ x, f (a x) = b (f x)) (y : H) (hy : b y = y) :
    ∃ x, a x = x ∧ f x = y := by
  obtain ⟨x, rfl⟩ := hf y
  obtain ⟨⟨u, v⟩, ⟨hu, hv, huv⟩, _⟩ :=
    Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card hG a ha x
  obtain ⟨w, hw, huniq⟩ :=
    Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card hH b hb (f x)
  have h1 : (f u, f v) = w := huniq _ ⟨by rw [← heq, hu],
    by rw [← heq, hv, map_inv], by rw [← map_mul, huv]⟩
  have h2 : (f x, 1) = w := huniq _ ⟨hy, by simp, by simp⟩
  exact ⟨u, hu, congrArg Prod.fst (h1.trans h2.symm)⟩
end MulAut
namespace MulAut
variable {G H : Type*} [Group G] [Group H]
public theorem exists_common_fixed_preimage_of_odd_card [Finite G] [Finite H]
    (hG : Odd (Nat.card G)) (hH : Odd (Nat.card H))
    (a b : MulAut G) (c d : MulAut H)
    (ha : Function.Involutive a) (hb : Function.Involutive b)
    (hc : Function.Involutive c) (hd : Function.Involutive d)
    (hab : Commute a b) (f : G →* H) (hf : Function.Surjective f)
    (hac : ∀ x, f (a x) = c (f x)) (hbd : ∀ x, f (b x) = d (f x))
    (y : H) (hyc : c y = y) (hyd : d y = y) :
    ∃ x, a x = x ∧ b x = x ∧ f x = y := by
  obtain ⟨x, hax, hfx⟩ := exists_fixed_preimage_of_odd_card hG hH a c ha hc f hf hac y hyc
  obtain ⟨⟨u, v⟩, ⟨hu, hv, huv⟩, huniq⟩ :=
    Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card hG b hb x
  have habx (z : G) : b (a z) = a (b z) :=
    (congrArg (fun e : MulAut G => e z) hab.eq).symm
  have hau : a u = u := congrArg Prod.fst (huniq (a u, a v)
    ⟨by rw [habx, hu], by rw [habx, hv, map_inv], by rw [← map_mul, huv, hax]⟩)
  obtain ⟨w, hw, hwuniq⟩ :=
    Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card hH d hd y
  have h1 : (f u, f v) = w := hwuniq _ ⟨by rw [← hbd, hu],
    by rw [← hbd, hv, map_inv], by rw [← map_mul, huv, hfx]⟩
  have h2 : (y, 1) = w := hwuniq _ ⟨hyd, by simp, by simp⟩
  exact ⟨u, hau, hu, congrArg Prod.fst (h1.trans h2.symm)⟩
end MulAut
