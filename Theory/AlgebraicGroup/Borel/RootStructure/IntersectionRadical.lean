module

public import Theory.AlgebraicGroup.Borel.Defs
public import Theory.AlgebraicGroup.Reductive.Defs
public import Theory.AlgebraicGroup.Unipotent.Radical

/-!
The first assertion of GLS3, Theorem 1.11.4: if two Borel subgroups of a
reductive algebraic group have unipotent radicals `U₀` and `U₁`, then
`U₀ ∩ U₁` is the unipotent radical of the Borel intersection.

Containment, unipotence, and normalization follow by restriction from the two
given radicals. For maximality, a closed unipotent subgroup of the intersection
lies in each Borel, hence in each unipotent radical by connected solvability of
Borel subgroups.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The intersection of the unipotent radicals of two Borel subgroups is the
unipotent radical of their intersection. -/
public theorem borel_intersection_isUnipotentRadicalOf
    {K : Variety k} [AlgebraicGroup K]
    (_hK : IsReductiveAlgebraicGroup K)
    (B₀ B₁ U₀ U₁ : ClosedSubgroup K)
    (hB₀ : IsBorelSubgroup B₀) (hB₁ : IsBorelSubgroup B₁)
    (hU₀ : IsUnipotentRadicalOf B₀ U₀)
    (hU₁ : IsUnipotentRadicalOf B₁ U₁) :
    IsUnipotentRadicalOf (B₀.inter B₁) (U₀.inter U₁) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨hU₀.1 hx.1, hU₁.1 hx.2⟩
  · intro z
    have hx₀ : (U₀.inter U₁).includePoint z ∈ U₀ := by
      change (↑((U₀.inter U₁).pointEquiv z) : Variety.Point K) ∈ U₀
      exact ((U₀.inter U₁).pointEquiv z).property.1
    have hxU₀ : IsUnipotentElement U₀.carrierVariety
        (U₀.pointEquiv.symm ⟨(U₀.inter U₁).includePoint z, hx₀⟩) := by
      apply hU₀.2.1
    have hxK : IsUnipotentElement K ((U₀.inter U₁).includePoint z) :=
      (closedSubgroup_unipotentElement_iff U₀ hx₀).mpr hxU₀
    apply (closedSubgroup_unipotentElement_iff (U₀.inter U₁)
      ((U₀.inter U₁).pointEquiv z).property).mp
    exact hxK
  · intro b hb u hu
    exact ⟨hU₀.2.2.1 b hb.1 u hu.1, hU₁.2.2.1 b hb.2 u hu.2⟩
  · intro V hV hVuni _hVnorm x hx
    have hVB₀ : V ≤ B₀ := fun y hy => (hV hy).1
    have hVB₁ : V ≤ B₁ := fun y hy => (hV hy).2
    exact ⟨hU₀.contains_unipotent_closedSubgroup hB₀.connected hB₀.solvable
        hVB₀ hVuni hx,
      hU₁.contains_unipotent_closedSubgroup hB₁.connected hB₁.solvable
        hVB₁ hVuni hx⟩

end Theory.AlgebraicGroup
