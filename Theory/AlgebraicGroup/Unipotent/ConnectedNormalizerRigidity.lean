module

public import Theory.AlgebraicGroup.Unipotent.Normalizer

/-!
In a connected unipotent group, a closed subgroup containing the identity
component of its normalizer is the whole group. Otherwise normalizer dimension
growth contradicts that containment. This is the rigidity step used to identify
the Borel-intersection radical in GLS3, §3.1, proof of Theorem 3.1.1(b), using
Proposition 1.3.2(d).
-/

universe u
namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A closed subgroup of a connected unipotent group which contains its
connected normalizer is the whole group. -/
public theorem IsUnipotentAlgebraicGroup.eq_top_of_normalizer_identityComponent_le
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsUnipotentAlgebraicGroup G) (hGc : Variety.IsConnected G)
    (H : ClosedSubgroup G) (hN : H.normalizer.identityComponentAmbient ≤ H) :
    H = ClosedSubgroup.top := by
  have htopDim : Variety.dimension (ClosedSubgroup.top : ClosedSubgroup G).carrierVariety =
      Variety.dimension G :=
    (closedSubgroup_dimension_eq_iff_contains_identityComponent G
      ClosedSubgroup.top).2 (fun _ _ => trivial)
  have hHle : Variety.dimension H.carrierVariety ≤ Variety.dimension G := by
    have h := connected_closedSubgroup_dimension_le_of_le
      H.identityComponentAmbient ClosedSubgroup.top
      H.identityComponentAmbient_isConnected (fun _ _ => trivial)
    simpa only [ClosedSubgroup.dimension_identityComponentAmbient, htopDim] using h
  have hdim : Variety.dimension H.carrierVariety = Variety.dimension G := by
    by_contra hne
    have hlt := hG.normalizer_dimension_gt H (lt_of_le_of_ne hHle hne)
    have hle := connected_closedSubgroup_dimension_le_of_le
      H.normalizer.identityComponentAmbient H
      H.normalizer.identityComponentAmbient_isConnected hN
    rw [ClosedSubgroup.dimension_identityComponentAmbient] at hle
    exact (not_le_of_gt hlt) hle
  have hcontains :=
    (closedSubgroup_dimension_eq_iff_contains_identityComponent G H).1 hdim
  rw [(identityComponent_eq_univ_iff_isConnected G).2 hGc] at hcontains
  apply SetLike.coe_injective
  exact Set.Subset.antisymm (fun _ _ => trivial) hcontains

end Theory.AlgebraicGroup
