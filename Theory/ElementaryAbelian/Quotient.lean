module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Images and quotients of elementary abelian groups

Commutativity and the exponent bound pass through surjective homomorphisms.
In particular, an actual quotient of an elementary abelian group remains
elementary abelian. This supports the module U/C_U(L) in short-group theory.
-/

public section

open scoped IsMulCommutative

theorem IsElementaryAbelian.of_surjective {p : ℕ} {G H : Type*}
    [Group G] [Group H] [IsElementaryAbelian p G]
    (f : G →* H) (hf : Function.Surjective f) : IsElementaryAbelian p H := by
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · intro x y
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    simpa only [map_mul] using congrArg f (mul_comm a b)
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro y
    obtain ⟨x, rfl⟩ := hf y
    rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p G) x, map_one]

instance IsElementaryAbelian.quotient {p : ℕ} {G : Type*} [Group G]
    [IsElementaryAbelian p G] (N : Subgroup G) [N.Normal] :
    IsElementaryAbelian p (G ⧸ N) :=
  IsElementaryAbelian.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
