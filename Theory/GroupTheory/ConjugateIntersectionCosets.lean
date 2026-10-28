module

public import Mathlib.GroupTheory.Index
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cosets inside a double coset

For a subgroup `H` and an element `r`, the subgroup of local elements `h` such
that `r * h * r⁻¹ ∈ H` controls the right cosets in `H * r * H`. Choosing
representatives of its right cosets gives actual equalities in the ambient
group. A finite upper bound on `H` and an injection into this intersection
give a bound on the number of representatives.

This is the elementary stabilizer argument underlying the double-coset
algorithm in Gebhardt, Experimental Mathematics 9 (2000), Section 2.
-/

namespace Subgroup
@[expose] public section

variable {G : Type*} [Group G]

/-- The stabilizer in `H` of the right coset `H * r`. -/
def conjugateIntersection (H : Subgroup G) (r : G) : Subgroup H :=
  H.comap ((MulAut.conj r).toMonoidHom.comp H.subtype)

@[simp] theorem mem_conjugateIntersection (H : Subgroup G) (r : G) (h : H) :
    h ∈ H.conjugateIntersection r ↔ r * h.val * r⁻¹ ∈ H := Iff.rfl

/-- Right-coset representatives of the intersection give representatives in
the double coset, with a multiplier in the original subgroup. -/
theorem conjugateIntersection_covers (H : Subgroup G) (r : G) (h : H) :
    ∃ k : H, r * h.val = k.val *
      (r * ((Quotient.out (Quotient.mk (QuotientGroup.rightRel
        (H.conjugateIntersection r)) h) : H) : G)) := by
  let K := H.conjugateIntersection r
  let q := Quotient.mk (QuotientGroup.rightRel K) h
  let t : H := q.out
  have hrel : QuotientGroup.rightRel K t h :=
    Quotient.exact (Quotient.out_eq q)
  have hmem : h * t⁻¹ ∈ K := QuotientGroup.rightRel_apply.mp hrel
  refine ⟨⟨r * (h * t⁻¹ : H).val * r⁻¹, hmem⟩, ?_⟩
  change r * h.val = (r * (h.val * t.val⁻¹) * r⁻¹) * (r * t.val)
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

/-- Unlike a bare natural-number index inequality, the finite ambient
hypothesis guarantees that this bound counts all cosets. -/
theorem index_le_of_card_le_of_embedding [Finite G] (K : Subgroup G)
    {m n : ℕ} (hm : 0 < m) (hcard : Nat.card G ≤ n * m)
    (e : Fin m ↪ K) : K.index ≤ n := by
  have hlow : m ≤ Nat.card K := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective e e.injective
  have hmul : K.index * m ≤ n * m := calc
    K.index * m ≤ K.index * Nat.card K := Nat.mul_le_mul_left _ hlow
    _ = Nat.card G := K.index_mul_card
    _ ≤ n * m := hcard
  exact Nat.le_of_mul_le_mul_right hmul hm

end
end Subgroup
