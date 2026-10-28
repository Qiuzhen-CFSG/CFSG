module

public import Theory.AlgebraicGroup.Bor1.IdentityComponentTangentSurjective
public import Theory.AlgebraicGroup.Bor1.IrreducibleTangentDimension
public import Theory.AlgebraicGroup.Dimension.Group

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option linter.style.haveILetI false in
/-- The identity tangent space of an algebraic group has the dimension of the
group, including when the group is disconnected. -/
public theorem identityPointDerivation_finrank_eq_dimension
    (G : Variety k) [AlgebraicGroup G] :
    Module.finrank k (IdentityPointDerivation G) =
      Cardinal.toNat (Variety.dimension G) := by
  let H := AlgebraicGroup.identityComponentClosedSubgroup G
  let d := identityTangentMorphismLinearMap H.inclusion
  have hd : Function.Bijective d :=
    ⟨identityTangentMorphismLinearMap_inclusion_injective H,
      identityComponent_inclusion_tangent_surjective G⟩
  let e : IdentityPointDerivation H.carrierVariety ≃ₗ[k]
      IdentityPointDerivation G := LinearEquiv.ofBijective d hd
  let hHirr := AlgebraicGroup.identityComponent_isIrreducible G
  let p := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  have hHcarrier : (H : Set (Variety.Point G)) =
      AlgebraicGroup.identityComponent G := by
    ext x
    rfl
  have hHirr' : IsIrreducible (H : Set (Variety.Point G)) := by
    rw [hHcarrier]
    exact hHirr
  letI : IrreducibleSpace
      {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    Subtype.irreducibleSpace hHirr'
  letI : IrreducibleSpace (Variety.Point H.carrierVariety) :=
    p.irreducibleSpace_iff.mpr inferInstance
  have hHuniv : IsIrreducible
      (Set.univ : Set (Variety.Point H.carrierVariety)) :=
    IrreducibleSpace.isIrreducible_univ _
  calc
    Module.finrank k (IdentityPointDerivation G) =
        Module.finrank k (IdentityPointDerivation H.carrierVariety) :=
      e.finrank_eq.symm
    _ = Cardinal.toNat (Variety.dimension H.carrierVariety) :=
      identityPointDerivation_finrank_eq_dimension_of_isIrreducible
        H.carrierVariety hHuniv
    _ = Cardinal.toNat (Variety.dimension G) := by
      rw [AlgebraicGroup.dimension_identityComponentClosedSubgroup G]

end Theory.AlgebraicGroup.Bor1
