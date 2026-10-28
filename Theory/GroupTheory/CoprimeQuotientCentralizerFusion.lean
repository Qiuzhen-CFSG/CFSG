module

public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Mathlib.Algebra.Group.Conj

/-!
# Centralizer membership under quotient-controlled fusion

If the image of a prime subgroup is normal modulo a coprime kernel,
conjugate elements in a common prime overgroup either both centralize the
subgroup or neither does. Injectivity on the prime overgroup identifies its
centralizer with the inverse image of the quotient centralizer. The latter
is normal because the quotient subgroup is normal.

This is the local fusion invariant needed in Janko--Thompson, Math. Z. 113
(1970), p.396, with the actual odd-core quotient of the omega normalizer.
-/

namespace Subgroup

/-- The centralizer of a subgroup with normal quotient image is invariant
under fusion returning to a common prime overgroup. -/
public theorem centralizer_mem_iff_of_normal_map_of_isConj
    {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H)
    (hker : Nat.Coprime p (Nat.card f.ker))
    (P A : Subgroup G) (hP : IsPGroup p P) (hAP : A ≤ P)
    [(A.map f).Normal] (x y : G) (hx : x ∈ P) (hy : y ∈ P)
    (hxy : IsConj x y) :
    x ∈ centralizer (A : Set G) ↔ y ∈ centralizer (A : Set G) := by
  let D := (centralizer (A.map f : Set H)).comap f
  have hD (u : G) (hu : u ∈ P) : u ∈ D ↔ u ∈ centralizer (A : Set G) := by
    constructor
    · intro h a ha
      have he := h (f a) (mem_map_of_mem f ha)
      have hEq : (⟨a * u, P.mul_mem (hAP ha) hu⟩ : P) =
          ⟨u * a, P.mul_mem hu (hAP ha)⟩ :=
        injective_comp_subtype_of_coprime_ker f hker P hP (by
          change f (a * u) = f (u * a)
          simpa only [map_mul] using he)
      exact congrArg Subtype.val hEq
    · rintro h _ ⟨a, ha, rfl⟩
      simpa only [map_mul] using congrArg f (h a ha)
  rw [← hD x hx, ← hD y hy]
  obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
  exact (mem_normalizer_iff.mp (show g ∈ normalizer (D : Set G) by
    rw [D.normalizer_eq_top]
    trivial) x)

end Subgroup
