module

public import Theory.AlgebraicGroup.Automorphisms.Lang.DerivedRestriction
public import Theory.AlgebraicGroup.Automorphisms.Lang.CommutativeSurjectivity
public import Theory.AlgebraicGroup.Automorphisms.Lang.FixedPointsInvariantQuotient
public import Theory.AlgebraicGroup.ClosedSubgroup.InvariantFiniteType

/-!
# Lang surjectivity for connected solvable algebraic groups

This module proves the solvable case of Lang's theorem: if `sigma` is a
surjective algebraic-group endomorphism of a connected solvable group and its
fixed-point subtype is finite, then `g ↦ g * sigma(g⁻¹)` is surjective.

The proof follows Steinberg, Theorem 10.4.  It uses well-founded induction on
dimension, which implements induction along the derived series.  The closed
derived subgroup is connected, `sigma`-stable, solvable, and has smaller
dimension unless the group is trivial.  The invariant normal quotient theorem
induces a Steinberg endomorphism on the commutative quotient, where the
commutative Lang theorem supplies a solution.  Lifting that solution leaves an
error in the derived closure, discharged by the induction hypothesis.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The Lang morphism of a Steinberg endomorphism of a connected solvable
algebraic group is surjective on rational points. -/
public theorem langMorphism_surjective_of_solvable
    {K : Variety k} [AlgebraicGroup K]
    (sigma : Morphism K K)
    (hsigma : IsAlgebraicSteinbergEndomorphism sigma)
    (hK : Variety.IsConnected K)
    (hsolvable : Group.IsSolvable (Variety.Point K)) :
    Function.Surjective (langMorphism sigma).toFun := by
  have main : forall d : Cardinal, forall (K : Variety k) [AlgebraicGroup K],
      Variety.dimension K = d ->
      (sigma : Morphism K K) -> IsAlgebraicSteinbergEndomorphism sigma ->
      Variety.IsConnected K -> Group.IsSolvable (Variety.Point K) ->
      Function.Surjective (langMorphism sigma).toFun := by
    intro d
    induction d using WellFoundedLT.induction with
    | ind d ih =>
      intro K _ hdim sigma hsigma hK hsolvable
      let D := derivedClosure K
      have hDnormal : D.toSubgroup.Normal := derivedClosure_normal K
      have hstable := derivedClosure_map sigma
      let _ : Algebra.FiniteType k (rightInvariantCoordinateRing D) :=
        D.rightInvariantCoordinateRing_finiteType inferInstance
      obtain ⟨Q, instQ, pi, tau, hpisurj, hpiker, hcompat, htau⟩ :=
        steinbergEndomorphism_invariantQuotient_exists sigma hsigma hK D hDnormal hstable
      let _ : AlgebraicGroup Q := instQ
      have hQconn : Variety.IsConnected Q := by
        have hi := hK.image pi.onPoints pi.toVariety.continuous.continuousOn
        rwa [Set.image_univ, hpisurj.range_eq] at hi
      have hQcomm : IsMulCommutative (Variety.Point Q) := by
        rw [isMulCommutative_iff]
        intro x y
        obtain ⟨a, rfl⟩ := hpisurj x
        obtain ⟨b, rfl⟩ := hpisurj y
        rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
        apply MonoidHom.mem_ker.mp
        change _ ∈ pi.kernel
        rw [hpiker]
        exact commutatorElement_mem_derivedClosure a b
      have hQlang := langMorphism_surjective_of_connected_commutative
        tau hQconn hQcomm htau.2
      intro x
      obtain ⟨q, hq⟩ := hQlang (pi.onPoints x)
      obtain ⟨y, hy⟩ := hpisurj q
      have hdmem : y⁻¹ * x * sigma.onPoints y ∈ D.toSubgroup := by
        rw [← hpiker]
        apply MonoidHom.mem_ker.mpr
        rw [map_mul, map_mul, map_inv, hcompat, hy]
        have hq' : q * (tau.onPoints q)⁻¹ = pi.onPoints x := by
          simpa [langMorphism_apply, map_inv] using hq
        rw [← hq']
        simp
      by_cases htriv : Subsingleton (Variety.Point K)
      · let _ := htriv
        refine ⟨1, Subsingleton.elim _ _⟩
      · let _ : Nontrivial (Variety.Point K) := not_subsingleton_iff_nontrivial.mp htriv
        have hDdimlt : Variety.dimension D.carrierVariety < d := by
          rw [← hdim]
          exact derivedClosure_dimension_lt_of_isSolvable hK hsolvable
        have hDlang := ih (Variety.dimension D.carrierVariety) hDdimlt
          D.carrierVariety rfl (derivedRestriction sigma)
          (derivedRestriction_steinbergEndomorphism sigma hsigma hK)
          (derivedClosure_connected hK) (derivedClosure_solvable hsolvable)
        let dpoint : Variety.Point D.carrierVariety := D.pointEquiv.symm ⟨_, hdmem⟩
        obtain ⟨z, hz⟩ := hDlang dpoint
        refine ⟨y * D.inclusion.onPoints z, ?_⟩
        have hz' := congrArg D.inclusion.onPoints hz
        simp only [langMorphism_apply, map_mul, mul_inv_rev, map_inv] at hz' ⊢
        rw [derivedRestriction_inclusion_apply] at hz'
        have hz'' : D.inclusion.onPoints z *
            (sigma.onPoints (D.inclusion.onPoints z))⁻¹ =
            D.inclusion.onPoints dpoint := by
          simpa [D] using hz'
        have hdpoint : D.inclusion.onPoints dpoint =
            y⁻¹ * x * sigma.onPoints y := by
          change (D.pointEquiv dpoint).1 = _
          exact congrArg Subtype.val
            (D.pointEquiv.apply_symm_apply ⟨_, hdmem⟩)
        calc
          y * D.inclusion.onPoints z *
                ((sigma.onPoints (D.inclusion.onPoints z))⁻¹ *
                (sigma.onPoints y)⁻¹) =
              y * (D.inclusion.onPoints z *
                (sigma.onPoints (D.inclusion.onPoints z))⁻¹) *
                (sigma.onPoints y)⁻¹ := by group
          _ = y * D.inclusion.onPoints dpoint * (sigma.onPoints y)⁻¹ := by
            rw [hz'']
          _ = x := by
            rw [hdpoint]
            group
  exact main (Variety.dimension K) K rfl sigma hsigma hK hsolvable

end Theory.AlgebraicGroup
