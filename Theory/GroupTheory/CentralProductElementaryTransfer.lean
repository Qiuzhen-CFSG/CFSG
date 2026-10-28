module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Transferring elementary subgroups between central products

Suppose `A` commutes with `R`, and a homomorphism from `R` into another
subgroup `K` commutes with `A` and preserves exactly the overlap with `A`.
Then every elementary subgroup of `A R` has an elementary copy of the same
order in `A K`.

The two multiplication maps from `A × R` have the same kernel. Their ranges
are consequently isomorphic, and this isomorphism transports the elementary
subgroup. No classification or finiteness assumption is needed.

This is the gluing argument in the quaternion-core reduction associated with
the binary remark following GLS, Number 2, Proposition 22.4.
-/

namespace Subgroup

/-- Replace one commuting factor by a homomorphic image with the same overlap,
preserving elementary subgroups and their cardinalities. -/
public theorem exists_elementary_subgroup_of_central_product_replacement
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (A R K B : Subgroup G)
    (hcomm : ∀ a : A, ∀ r : R, Commute (a : G) (r : G))
    (f : R →* G) (hfK : f.range ≤ K)
    (hfcomm : ∀ a : A, ∀ r : R, Commute (a : G) (f r))
    (hcompat : ∀ a : A, ∀ r : R, (a : G) = (r : G) ↔ (a : G) = f r)
    (hB : B ≤ A ⊔ R) [IsElementaryAbelian p B] :
    ∃ D : Subgroup G, D ≤ A ⊔ K ∧ IsElementaryAbelian p D ∧
      Nat.card D = Nat.card B := by
  let u : A × R →* G := A.subtype.noncommCoprod R.subtype hcomm
  let v : A × R →* G := A.subtype.noncommCoprod f hfcomm
  have hu : u.range = A ⊔ R := by
    exact (MonoidHom.noncommCoprod_range _ _ _).trans
      (by rw [A.range_subtype, R.range_subtype])
  have hv : v.range ≤ A ⊔ K := by
    rw [show v.range = A ⊔ f.range from
      (MonoidHom.noncommCoprod_range _ _ _).trans (by rw [A.range_subtype])]
    exact sup_le_sup_left hfK A
  have hker : u.ker = v.ker := by
    ext x
    change (x.1 : G) * (x.2 : G) = 1 ↔ (x.1 : G) * f x.2 = 1
    simpa only [mul_eq_one_iff_eq_inv, map_inv, coe_inv] using hcompat x.1 x.2⁻¹
  let e : u.range ≃* v.range := (QuotientGroup.quotientKerEquivRange u).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivRange v))
  have hBu : B ≤ u.range := hu.symm ▸ hB
  let B' : Subgroup u.range := B.subgroupOf u.range
  let g : u.range →* G := v.range.subtype.comp e.toMonoidHom
  have hg : Function.Injective g := v.range.subtype_injective.comp e.injective
  let : IsElementaryAbelian p B' := IsElementaryAbelian.subgroupOf hBu
  refine ⟨B'.map g, ?_, IsElementaryAbelian.map g, ?_⟩
  · rintro x ⟨y, _, rfl⟩
    exact hv (e y).property
  · rw [card_map_of_injective hg]
    exact Nat.card_congr (subgroupOfEquivOfLe hBu).toEquiv

end Subgroup
