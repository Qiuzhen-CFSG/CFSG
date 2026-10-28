module

public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# Intersections with the prime-to-p residual

If a normal subgroup N contains O^{p′}(G), intersecting any subgroup H
with N preserves the embedded prime-to-p residual of H. Functoriality
places O^{p′}(H) in N, and normal restriction gives the equality.
Applying this inside an overgroup gives the corresponding equality for
intersections with its embedded residual in a larger ambient group.

This supplies the residual-centralizer comparison in Aschbacher–Smith,
combined 1 March 2004 manuscript, printed p.933, after Lemma 13.6.23.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Intersecting with a normal subgroup containing the ambient residual
preserves the embedded residual of every subgroup. -/
theorem embedded_primeToResidual_inf_eq_of_normal (p : ℕ) [Fact p.Prime]
    (N H : Subgroup G) [N.Normal] (hN : primeToResidual p G ≤ N) :
    (primeToResidual p (N ⊓ H : Subgroup G)).map (N ⊓ H).subtype =
      (primeToResidual p H).map H.subtype := by
  have h : primeToResidual p H ≤ N.subgroupOf H := by
    intro x hx
    exact hN (map_primeToResidual_le_of_hom p H.subtype (mem_map_of_mem _ hx))
  have he := congrArg (fun U : Subgroup H => U.map H.subtype)
    (embedded_primeToResidual_eq_of_normal p (N.subgroupOf H) h)
  rwa [map_embedded_primeToResidual_of_hom, subgroupOf_map_subtype] at he

/-- The residual of the intersection with O^{p′}(H) equals that of the
intersection with H. Both residuals retain their original ambient embedding. -/
theorem embedded_primeToResidual_intersection (p : ℕ) [Fact p.Prime]
    (H D : Subgroup G) :
    (primeToResidual p (((primeToResidual p H).map H.subtype) ⊓ D : Subgroup G)).map
      (((primeToResidual p H).map H.subtype) ⊓ D).subtype =
      (primeToResidual p (H ⊓ D : Subgroup G)).map (H ⊓ D).subtype := by
  have he := congrArg (fun U : Subgroup H => U.map H.subtype)
    (embedded_primeToResidual_inf_eq_of_normal p (primeToResidual p H)
      (D.subgroupOf H) le_rfl)
  rw [map_embedded_primeToResidual_of_hom,
    map_embedded_primeToResidual_of_hom,
    map_inf _ _ _ H.subtype_injective, subgroupOf_map_subtype] at he
  have hi : (primeToResidual p H).map H.subtype ⊓ (D ⊓ H) =
      (primeToResidual p H).map H.subtype ⊓ D := by
    exact le_antisymm (inf_le_inf_left _ inf_le_left)
      (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans (map_subtype_le _))))
  rw [hi, inf_comm D H] at he
  exact he

end Subgroup
