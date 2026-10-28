module

public import Theory.AlgebraicGroup.Bor1.TangentVanishingIdeal
public import Theory.AlgebraicGroup.ClosedSubgroup.IntersectionCharZero
public import Theory.AlgebraicGroup.Morphism.CodRestrict

/-!
# Tangent ranges for closed-subgroup intersections

This module isolates the formal part of the closed-subgroup intersection
argument.  The inclusion of `B.inter C` into each factor is obtained by the
explicit carrier algebraic-group and `codRestrictClosedSubgroup` constructions;
functoriality of the identity differential then gives the easy range
inclusion.  The reverse inclusion is reduced, through
`identityTangent_inclusion_range_iff_vanishingIdeal`, to the vanishing-ideal
sum condition
`(B.inter C).vanishingIdeal ≤ B.vanishingIdeal ⊔ C.vanishingIdeal`.

The imported characteristic-zero intersection bridge equips the quotient by
the ideal sum with a finite-type Hopf algebra structure.  Cartier reducedness,
followed by the Nullstellensatz comparison with the pointwise intersection,
supplies the ideal condition unconditionally.  The exact tangent-intersection
theorem below is therefore available for every pair of closed subgroups in
characteristic zero; the reduced-quotient endpoint is retained as a more
general reusable interface.
-/

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-! The formal inclusion direction, independent of any smooth-intersection
hypothesis. -/

public theorem identityTangent_range_inter_le
    {G : Variety k} [AlgebraicGroup G] (B C : ClosedSubgroup G) :
    LinearMap.range (identityTangentMorphismLinearMap (B.inter C).inclusion) ≤
      LinearMap.range (identityTangentMorphismLinearMap B.inclusion) ⊓
        LinearMap.range (identityTangentMorphismLinearMap C.inclusion) := by
  let I := B.inter C
  let hBmap : ∀ x : I.carrierVariety.Point, I.inclusion.onPoints x ∈ B.toSubgroup :=
    fun x =>
      ((ClosedSubgroup.mem_inter_iff B C (I.inclusion.onPoints x)).mp
        ((I.pointEquiv x).property)).1
  let hCmap : ∀ x : I.carrierVariety.Point, I.inclusion.onPoints x ∈ C.toSubgroup :=
    fun x =>
      ((ClosedSubgroup.mem_inter_iff B C (I.inclusion.onPoints x)).mp
        ((I.pointEquiv x).property)).2
  let iB : AlgebraicGroup.Morphism I.carrierVariety B.carrierVariety :=
    I.inclusion.codRestrictClosedSubgroup B hBmap
  let iC : AlgebraicGroup.Morphism I.carrierVariety C.carrierVariety :=
    I.inclusion.codRestrictClosedSubgroup C hCmap
  have hB : B.inclusion.comp iB = I.inclusion := by
    apply Morphism.ext
    funext x
    exact (Morphism.codRestrictClosedSubgroup_inclusion_apply
      I.inclusion B hBmap x).symm
  have hC : C.inclusion.comp iC = I.inclusion := by
    apply Morphism.ext
    funext x
    exact (Morphism.codRestrictClosedSubgroup_inclusion_apply
      I.inclusion C hCmap x).symm
  intro D hD
  apply (Submodule.mem_inf).2
  constructor
  · obtain ⟨E, rfl⟩ := hD
    refine ⟨identityTangentMorphismLinearMap iB E, ?_⟩
    rw [← LinearMap.comp_apply, ← identityTangentMorphismLinearMap_comp, hB]
  · obtain ⟨E, rfl⟩ := hD
    refine ⟨identityTangentMorphismLinearMap iC E, ?_⟩
    rw [← LinearMap.comp_apply, ← identityTangentMorphismLinearMap_comp, hC]

/-! The missing scheme-theoretic input is consumed only through the vanishing
ideal criterion. -/

public theorem identityTangent_range_inf_le_of_vanishingIdeal_sup
    {G : Variety k} [AlgebraicGroup G] (B C : ClosedSubgroup G)
    (hI : (B.inter C).vanishingIdeal ≤ B.vanishingIdeal ⊔ C.vanishingIdeal) :
    LinearMap.range (identityTangentMorphismLinearMap B.inclusion) ⊓
        LinearMap.range (identityTangentMorphismLinearMap C.inclusion) ≤
      LinearMap.range (identityTangentMorphismLinearMap (B.inter C).inclusion) := by
  intro D hD
  have hD' := (Submodule.mem_inf.mp hD)
  have hB : ∀ f ∈ B.vanishingIdeal, D f = 0 :=
    (identityTangent_inclusion_range_iff_vanishingIdeal B D).mp hD'.1
  have hC : ∀ f ∈ C.vanishingIdeal, D f = 0 :=
    (identityTangent_inclusion_range_iff_vanishingIdeal C D).mp hD'.2
  apply (identityTangent_inclusion_range_iff_vanishingIdeal (B.inter C) D).mpr
  intro f hf
  rcases Submodule.mem_sup.mp (hI hf) with ⟨b, hb, c, hc, hbc⟩
  rw [← hbc, map_add, hB b hb, hC c hc, add_zero]

public theorem identityTangent_range_eq_inf_of_vanishingIdeal_sup
    {G : Variety k} [AlgebraicGroup G] (B C : ClosedSubgroup G)
    (hI : (B.inter C).vanishingIdeal ≤ B.vanishingIdeal ⊔ C.vanishingIdeal) :
    LinearMap.range (identityTangentMorphismLinearMap (B.inter C).inclusion) =
      LinearMap.range (identityTangentMorphismLinearMap B.inclusion) ⊓
        LinearMap.range (identityTangentMorphismLinearMap C.inclusion) := by
  apply le_antisymm
  · exact identityTangent_range_inter_le B C
  · exact identityTangent_range_inf_le_of_vanishingIdeal_sup B C hI

/-- Exact tangent control follows as soon as the scheme-theoretic intersection
quotient is reduced. -/
public theorem identityTangent_range_eq_inf_of_intersectionQuotient_isReduced
    {G : Variety k} [AlgebraicGroup G] (B C : ClosedSubgroup G)
    (hred : IsReduced
      (G.PolynomialFunction ⧸ (B.vanishingIdeal ⊔ C.vanishingIdeal))) :
    LinearMap.range (identityTangentMorphismLinearMap (B.inter C).inclusion) =
      LinearMap.range (identityTangentMorphismLinearMap B.inclusion) ⊓
        LinearMap.range (identityTangentMorphismLinearMap C.inclusion) := by
  exact identityTangent_range_eq_inf_of_vanishingIdeal_sup B C
    (ClosedSubgroup.inter_vanishingIdeal_le_sup_of_isReduced B C hred)

/-- In characteristic zero, the identity tangent range of an intersection of
closed algebraic subgroups is exactly the intersection of their tangent
ranges. -/
public theorem identityTangent_range_eq_inf_charZero
    [CharZero k] {G : Variety k} [AlgebraicGroup G]
    (B C : ClosedSubgroup G) :
    LinearMap.range (identityTangentMorphismLinearMap (B.inter C).inclusion) =
      LinearMap.range (identityTangentMorphismLinearMap B.inclusion) ⊓
        LinearMap.range (identityTangentMorphismLinearMap C.inclusion) := by
  exact identityTangent_range_eq_inf_of_vanishingIdeal_sup B C
    (ClosedSubgroup.inter_vanishingIdeal_le_sup_charZero B C)

end Theory.AlgebraicGroup.Bor1
