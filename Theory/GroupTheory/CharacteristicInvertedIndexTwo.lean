module

public import Theory.GroupTheory.InvertedIndexTwo
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Splitting a characteristic inverted subgroup of index two

All elements outside an inverted subgroup of index two have the same square.
When the subgroup is characteristic, this square is fixed by every
automorphism. Inversion also makes its order divide two. Thus the absence
of a characteristic subgroup of order two forces every outside inverter
to be an involution.

This is the nonsplit-extension exclusion in the order-thirty-two argument
of Janko–Thompson, Math. Z. 113 (1970), results 1.3–1.4, printed p.386.
-/

namespace Subgroup

/-- An outside inverter of a characteristic index-two subgroup is an
involution if the ambient group has no characteristic subgroup of order two. -/
public theorem sq_eq_one_of_characteristic_inverted_index_two
    {G : Type*} [Group G]
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (A : Subgroup G) [A.Characteristic] (hi : A.index = 2)
    (t : G) (ht : t ∉ A) (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹) :
    t ^ 2 = 1 := by
  have hfix (f : MulAut G) : f (t ^ 2) = t ^ 2 := by
    rw [map_pow]
    apply sq_eq_of_inverted_index_two A hi ht _ hinv
    intro hf
    apply ht
    have hmem : f.symm (f t) ∈ A :=
      characteristic_iff_le_comap.mp inferInstance f.symm hf
    simpa using hmem
  have hc : (zpowers (t ^ 2)).Characteristic := by
    apply characteristic_iff_map_eq.mpr
    intro f
    rw [MonoidHom.map_zpowers]
    change zpowers (f (t ^ 2)) = zpowers (t ^ 2)
    rw [hfix]
  have hinv' : t ^ 2 = (t ^ 2)⁻¹ := by
    calc
      t ^ 2 = t * t ^ 2 * t⁻¹ := by group
      _ = (t ^ 2)⁻¹ := hinv _ (A.sq_mem_of_index_two hi t)
  have hp : (t ^ 2) ^ 2 = 1 := by
    exact (pow_two _).trans
      ((congrArg (fun x : G => x * t ^ 2) hinv').trans (inv_mul_cancel _))
  by_contra hn
  apply hchar (zpowers (t ^ 2)) hc
  rw [Nat.card_zpowers, orderOf_eq_prime hp hn]

end Subgroup
