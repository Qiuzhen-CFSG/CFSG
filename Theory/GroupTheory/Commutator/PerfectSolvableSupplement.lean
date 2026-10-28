module
public import Theory.GroupTheory.SolvableResidual
public import Mathlib.GroupTheory.IsSubnormal

/-!
# Solvable supplements of perfect subnormal subgroups

If a perfect subnormal subgroup normalizes a solvable subgroup, it is the
solvable residual of their join. Consequently the solvable subgroup normalizes
it in return. The proof inducts along a subnormal chain: the quotient of each
intermediate subgroup by the preceding subgroup is a solvable image of the
supplement, and therefore contains no nontrivial perfect image.

This strengthens the C-component assertion in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Proposition A.3.3(3), p. 42
(1 March 2004 manuscript).
-/

@[expose] public section
namespace Subgroup
variable {G : Type*} [Group G]

private theorem solvable_quotient_of_solvable_supplement
    (H N K : Subgroup G) [N.Normal] [Group.IsSolvable N]
    (hsup : H ⊔ N = ⊤) (hHK : H ≤ K) [(H.subgroupOf K).Normal] :
    Group.IsSolvable (K ⧸ H.subgroupOf K) := by
  let q := QuotientGroup.mk' (H.subgroupOf K)
  let f : N.subgroupOf K →* K ⧸ H.subgroupOf K := q.comp (N.subgroupOf K).subtype
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (H.subgroupOf K) y
    have hk : (k : G) ∈ H ⊔ N := by rw [hsup]; trivial
    obtain ⟨h, hh, n, hn, he⟩ := mem_sup_of_normal_right.mp hk
    have hnK : n ∈ K := by
      have : h⁻¹ * (k : G) ∈ K := K.mul_mem (K.inv_mem (hHK hh)) k.property
      simpa only [← he, inv_mul_cancel_left] using this
    refine ⟨⟨⟨n, hnK⟩, hn⟩, ?_⟩
    have heK : (⟨h, hHK hh⟩ : K) * ⟨n, hnK⟩ = k := Subtype.ext he
    have hqh : q ⟨h, hHK hh⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hh
    change q ⟨n, hnK⟩ = q k
    rw [← heK, map_mul, hqh, one_mul]
  let : Group.IsSolvable (N.subgroupOf K) :=
    Group.isSolvable_of_isSolvable_injective (f := K.subtype.subgroupComap N)
      (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun x : N => (x : G)) hab)))
  exact Group.isSolvable_of_surjective hf

/-- A subnormal subgroup supplemented by a solvable normal subgroup contains the residual. -/
theorem IsSubnormal.solvableResidual_le_of_sup_eq_top [Finite G]
    {H : Subgroup G} (hH : H.IsSubnormal) (N : Subgroup G)
    [N.Normal] [Group.IsSolvable N] (hsup : H ⊔ N = ⊤) :
    solvableResidual G ≤ H := by
  induction hH with
  | top => exact le_top
  | step H K hHK hK hnormal ih =>
    have hKN : K ⊔ N = ⊤ := top_unique (hsup ▸ sup_le_sup_right hHK N)
    have hRK : solvableResidual G ≤ K := ih hKN
    let := hnormal
    let : Group.IsSolvable (K ⧸ H.subgroupOf K) :=
      solvable_quotient_of_solvable_supplement H N K hsup hHK
    have hRH := solvableResidual_le_of_solvable_quotient (H.subgroupOf K)
    exact (le_map_solvableResidual_of_isPerfect _ K hRK).trans (by
      simpa only [map_subgroupOf_eq_of_le hHK] using map_mono (f := K.subtype) hRH)

/-- A perfect subnormal subgroup supplemented by a solvable normal subgroup is the residual. -/
theorem IsSubnormal.eq_solvableResidual_of_sup_eq_top [Finite G]
    {H : Subgroup G} (hH : H.IsSubnormal) [Group.IsPerfect H] (N : Subgroup G)
    [N.Normal] [Group.IsSolvable N] (hsup : H ⊔ N = ⊤) : H = solvableResidual G :=
  le_antisymm (le_solvableResidual_of_isPerfect H)
    (hH.solvableResidual_le_of_sup_eq_top N hsup)

/-- The residual of a perfect subnormal subgroup with an invariant solvable supplement. -/
theorem IsSubnormal.solvableResidual_sup_eq [Finite G]
    {L : Subgroup G} (hL : L.IsSubnormal) [Group.IsPerfect L]
    (N : Subgroup G) [Group.IsSolvable N] (hLN : L ≤ normalizer N) :
    (solvableResidual ↥(L ⊔ N)).map (L ⊔ N).subtype = L := by
  let H := L ⊔ N
  have hLH : L ≤ H := le_sup_left
  let : (N.subgroupOf H).Normal := normal_subgroupOf_sup_of_le_normalizer hLN
  let : Group.IsPerfect (L.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hLH).symm.toMonoidHom)
      (subgroupOfEquivOfLe hLH).symm.surjective
  let : Group.IsSolvable (N.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show N ≤ H from le_sup_right)).toMonoidHom)
      (subgroupOfEquivOfLe (show N ≤ H from le_sup_right)).injective
  have he := hL.subgroupOf.eq_solvableResidual_of_sup_eq_top (N.subgroupOf H)
    (codisjoint_subgroupOf_sup L N).eq_top
  rw [← he, map_subgroupOf_eq_of_le hLH]

/-- An invariant solvable subgroup normalizes any finite perfect subnormal subgroup. -/
theorem IsSubnormal.commutator_le_of_solvable [Finite G]
    {L : Subgroup G} (hL : L.IsSubnormal) [Group.IsPerfect L]
    (N : Subgroup G) [Group.IsSolvable N] (hLN : L ≤ normalizer N) : ⁅L, N⁆ ≤ L := by
  have hres := hL.solvableResidual_sup_eq N hLN
  have hn : (L.subgroupOf (L ⊔ N)).Normal := by
    have he : L.subgroupOf (L ⊔ N) = solvableResidual ↥(L ⊔ N) := by
      apply (map_injective (L ⊔ N).subtype_injective)
      rw [map_subgroupOf_eq_of_le le_sup_left, hres]
    rw [he]
    infer_instance
  have hnorm : L ⊔ N ≤ normalizer L := (normal_subgroupOf_iff_le_normalizer le_sup_left).mp hn
  exact le_normalizer_iff_commutator_le_left.mp (le_sup_right.trans hnorm)

end Subgroup
