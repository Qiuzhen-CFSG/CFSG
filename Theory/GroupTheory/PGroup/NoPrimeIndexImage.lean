module
public import Theory.GroupTheory.PGroup.TrivialImage

/-!
# Equal subgroup images through p-group kernels

In a finite group, two normal subgroups without normal subgroups of index p
are equal if their images under a homomorphism with p-group kernel agree.
The codomain need not be finite and the map need not be surjective; neither
centrality of the kernel nor perfectness of the subgroups is required.

For one containment, project into the quotient by the second subgroup.
Equality of images puts the first subgroup's image inside the image of the
original p-group kernel. The no-prime-index trivial-image theorem kills this
restricted quotient map. Apply the same argument in the opposite direction.

This is the residual uniqueness transfer needed for the normal SL2 subgroup
in Alperin--Brauer--Gorenstein, Chapter II, Section 3, Proposition 2
(article pages 22--23). It includes the nonperfect field-order-three case
through the existing no-index-two theorem.
-/

namespace Subgroup

private theorem le_of_map_le_of_no_normal_index_prime
    {G Q : Type*} [Group G] [Finite G] [Group Q]
    {p : ℕ} [Fact p.Prime] (f : G →* Q) (hker : IsPGroup p f.ker)
    (L M : Subgroup G) [M.Normal]
    (hL : ∀ K : Subgroup L, K.Normal → K.index ≠ p)
    (hmap : L.map f ≤ M.map f) : L ≤ M := by
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let P : Subgroup (G ⧸ M) := f.ker.map q
  have hP : IsPGroup p P := hker.map q
  have hmem (x : L) : q x ∈ P := by
    obtain ⟨y, hy, hxy⟩ := hmap (mem_map_of_mem f x.property)
    have hk : (x : G) * y⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
    refine ⟨(x : G) * y⁻¹, hk, ?_⟩
    have hqy : q y = 1 := (QuotientGroup.eq_one_iff (N := M) (x := y)).mpr hy
    rw [map_mul, map_inv, hqy, inv_one, mul_one]
  let r : L →* P := (q.comp L.subtype).codRestrict P hmem
  intro x hx
  have h := MonoidHom.eq_one_of_no_normal_index_prime hL hP r ⟨x, hx⟩
  exact (QuotientGroup.eq_one_iff (N := M) (x := x)).mp (congrArg Subtype.val h)

/-- A p-group kernel cannot identify distinct normal subgroups without
normal subgroups of index p. -/
public theorem eq_of_map_eq_of_no_normal_index_prime
    {G Q : Type*} [Group G] [Finite G] [Group Q]
    {p : ℕ} [Fact p.Prime] (f : G →* Q) (hker : IsPGroup p f.ker)
    (L M : Subgroup G) [L.Normal] [M.Normal]
    (hL : ∀ K : Subgroup L, K.Normal → K.index ≠ p)
    (hM : ∀ K : Subgroup M, K.Normal → K.index ≠ p)
    (hmap : L.map f = M.map f) : L = M := by
  exact le_antisymm (le_of_map_le_of_no_normal_index_prime f hker L M hL hmap.le)
    (le_of_map_le_of_no_normal_index_prime f hker M L hM hmap.ge)

end Subgroup

