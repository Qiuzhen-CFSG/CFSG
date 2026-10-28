module

public import Theory.AlgebraicGroup.Jordan.ClosedSubgroup
public import Theory.AlgebraicGroup.Tori.DiagonalizableClosedSubgroup
public import Theory.AlgebraicGroup.Tori.Semisimple

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Every point of a diagonalizable closed subgroup is semisimple in the
closed subgroup itself. -/
public theorem IsDiagonalizableClosedSubgroup.all_semisimple
    {G : Variety k} [AlgebraicGroup G] {S : ClosedSubgroup G}
    (hS : IsDiagonalizableClosedSubgroup S) :
    ∀ x : Variety.Point S.carrierVariety,
      IsSemisimpleElement S.carrierVariety x := by
  obtain ⟨n, D, ⟨e⟩⟩ := hS
  let : AlgebraicGroup D.carrierVariety := D.carrierAlgebraicGroup
  intro x
  let y : Variety.Point D.carrierVariety := e.hom.onPoints x
  have hyAmbient : IsSemisimpleElement (dVariety k n)
      (D.inclusion.onPoints y) :=
    dVariety_all_semisimple n (D.inclusion.onPoints y)
  have hy : IsSemisimpleElement D.carrierVariety y := by
    have hmem : D.inclusion.onPoints y ∈
        (D : Set (Variety.Point (dVariety k n))) :=
      (D.pointEquiv y).property
    have hsub :=
      (closedSubgroup_semisimpleElement_iff D hmem).mp hyAmbient
    have hpoint :
        D.pointEquiv.symm ⟨D.inclusion.onPoints y, hmem⟩ = y := by
      apply D.pointEquiv.injective
      rw [D.pointEquiv.apply_symm_apply]
      apply Subtype.ext
      rfl
    rw [hpoint] at hsub
    exact hsub
  have hback := morphism_preserves_semisimpleElement e.inv y hy
  simpa only [y, e.hom_inv_id] using hback

end Theory.AlgebraicGroup
