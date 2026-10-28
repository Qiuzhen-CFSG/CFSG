module

public import Theory.AlgebraicGroup.Automorphisms.Lang.SolvableSurjectivity
public import Theory.AlgebraicGroup.Automorphisms.SteinbergPositiveRootFactorOrbits
public import Theory.AlgebraicGroup.Borel.Defs

universe u

/-!
# The positive-root factor criterion for Steinberg endomorphisms

This module assembles the positive-root part of Steinberg,
*Endomorphisms of Linear Algebraic Groups*, Theorem 10.5, as quoted in GLS3,
Chapter 2.  The group is semisimple, `B` is an invariant Borel, and `T` is an
invariant maximal torus in `B`.  An actual based root-datum realization and
realized one-parameter root-subgroup witnesses produce a permutation of the
positive roots and pullback factors `p ^ m`, with `m : Nat`.

Finite ambient fixed points descend to the restriction on `T`.  Since a torus
is connected and solvable, Steinberg 10.4 makes its Lang map surjective.  The
orbit-sum argument then excludes an orbit on which every exponent is zero:
its nontrivial product character would be fixed by pullback, contradicting
Lang surjectivity.  The order of the root permutation is consequently one
common positive iterate with strictly positive accumulated exponent on every
positive-root orbit.
-/

open scoped BigOperators

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private theorem restricted_steinberg_of_invariant_closedSubgroup
    {K : Variety k} [AlgebraicGroup K] (H : ClosedSubgroup K)
    (sigma : AlgebraicGroup.Morphism K K)
    (hsigma : IsAlgebraicSteinbergEndomorphism sigma)
    (hsigmaH : sigma.onPoints '' (H : Set (Variety.Point K)) =
      (H : Set (Variety.Point K)))
    (tau : AlgebraicGroup.Morphism H.carrierVariety H.carrierVariety)
    (htau : ∀ x, H.includePoint (tau.onPoints x) =
      sigma.onPoints (H.includePoint x)) :
    IsAlgebraicSteinbergEndomorphism tau := by
  have hsurjective : Function.Surjective tau.onPoints := by
    intro y
    have hy : H.includePoint y ∈ (H : Set (Variety.Point K)) :=
      (H.pointEquiv y).property
    rw [← hsigmaH] at hy
    obtain ⟨x, hxH, hx⟩ := hy
    let xH : Variety.Point H.carrierVariety := H.pointEquiv.symm ⟨x, hxH⟩
    refine ⟨xH, ?_⟩
    apply H.inclusion_injective
    change H.includePoint (tau.onPoints xH) = H.includePoint y
    rw [htau]
    calc
      sigma.onPoints (H.includePoint xH) = sigma.onPoints x := by
        congr 1
      _ = H.includePoint y := hx
  have hfixed : Finite
      {x : Variety.Point H.carrierVariety | tau.onPoints x = x} := by
    let fixedToAmbient :
        {x : Variety.Point H.carrierVariety | tau.onPoints x = x} →
          {x : Variety.Point K | sigma.onPoints x = x} :=
      fun x => ⟨H.includePoint x, by
        change sigma.onPoints (H.includePoint x) = H.includePoint x
        rw [← htau]
        exact congrArg H.includePoint x.property⟩
    let _ := hsigma.2
    exact Finite.of_injective fixedToAmbient (by
      intro x y hxy
      apply Subtype.ext
      have hxy' := congrArg
        (fun z : {x : Variety.Point K | sigma.onPoints x = x} =>
          (z : Variety.Point K)) hxy
      apply H.inclusion_injective
      change H.includePoint (x : Variety.Point H.carrierVariety) =
        H.includePoint (y : Variety.Point H.carrierVariety)
      simpa [fixedToAmbient] using hxy')
  exact ⟨hsurjective, hfixed⟩

/-- In the invariant Borel--torus setting of Steinberg 10.5, the realized
root-subgroup factors give a positive-root permutation and a common positive
iterate whose Frobenius exponent is positive on every positive-root orbit. -/
public theorem exists_positive_root_iterate_factor_of_steinberg
    {K : Variety k} [AlgebraicGroup K]
    {T B : ClosedSubgroup K} (D : RootGroupData K T) [Finite D.Root]
    {ι X Y : Type*} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) [P.IsRootSystem]
    (base : P.Base) (e : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T)
    (positiveRoots : Set D.Root)
    (hActual : IsActualBasedRootDatum D P base e weightEquiv positiveRoots)
    (hD : D.IsRealization)
    (hpositiveSubgroup : ∀ α, α ∈ positiveRoots ↔ D.rootSubgroup α ≤ B)
    (_hB : IsBorelSubgroup B) (hT : IsMaximalTorus T) (_hTB : T ≤ B)
    (hK : IsSemisimpleAlgebraicGroup K)
    (sigma : AlgebraicGroup.Morphism K K)
    (hsigma : IsAlgebraicSteinbergEndomorphism sigma)
    (hsigmaB : sigma.onPoints '' (B : Set (Variety.Point K)) =
      (B : Set (Variety.Point K)))
    (hsigmaT : sigma.onPoints '' (T : Set (Variety.Point K)) =
      (T : Set (Variety.Point K)))
    (tau : AlgebraicGroup.Morphism T.carrierVariety T.carrierVariety)
    (htau : ∀ s, T.includePoint (tau.onPoints s) =
      sigma.onPoints (T.includePoint s))
    (hroot : ∀ α, Nonempty (RootSubgroupFrobeniusWitness D sigma α)) :
    ∃ rootPerm : Equiv.Perm D.Root, ∃ exponent : D.Root → ℕ, ∃ n : ℕ,
      0 < n ∧ rootPerm ^ n = 1 ∧
      (∀ α, α ∈ positiveRoots ↔ rootPerm α ∈ positiveRoots) ∧
      (∀ α,
        TorusCharacter.pullback tau (D.rootWeight (rootPerm α)) =
          D.rootWeight α ^ (ringChar k ^ exponent α)) ∧
      ∀ α ∈ positiveRoots,
        0 < ∑ i ∈ Finset.range n, exponent ((rootPerm ^ i) α) ∧
          ((TorusCharacter.pullback tau : TorusWeight T → TorusWeight T)^[n])
              (D.rootWeight α) =
            D.rootWeight α ^
              (ringChar k ^
                ∑ i ∈ Finset.range n, exponent ((rootPerm ^ i) α)) := by
  have htauSteinberg : IsAlgebraicSteinbergEndomorphism tau :=
    restricted_steinberg_of_invariant_closedSubgroup T sigma hsigma hsigmaT
      tau htau
  have hTsolvable : Group.IsSolvable
      (Variety.Point T.carrierVariety) :=
    Group.isSolvable_of_comm
      (isMulCommutative_iff.mp hT.1.isMulCommutative)
  have hLang : Function.Surjective (langMorphism tau).toFun :=
    langMorphism_surjective_of_solvable tau htauSteinberg
      hT.1.isConnected hTsolvable
  obtain ⟨rootPerm, exponent, hpositive, hfactor⟩ :=
    exists_surjective_root_frobenius_factors D P base e weightEquiv
      positiveRoots hActual hD hpositiveSubgroup hK sigma hsigma.1 hsigmaB
      tau htau hroot
  obtain ⟨n, hn, hperm, hiterate⟩ :=
    exists_positive_root_iterate_factor D P base e weightEquiv positiveRoots
      hActual tau hLang rootPerm exponent hpositive hfactor
  exact ⟨rootPerm, exponent, n, hn, hperm, hpositive, hfactor, hiterate⟩

end Theory.AlgebraicGroup
