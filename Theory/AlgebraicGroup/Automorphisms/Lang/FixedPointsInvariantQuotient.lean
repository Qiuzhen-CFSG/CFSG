module

public import Theory.AlgebraicGroup.Automorphisms.Lang.FiniteFixedFromOpenRange
public import Theory.AlgebraicGroup.ClosedSubgroup.InvariantFiniteType
public import Theory.AlgebraicGroup.ClosedSubgroup.InvariantQuotient

/-!
# Fixed points on an invariant quotient

This module proves Steinberg's Theorem 10.3 for a connected algebraic group.
Given a normal closed subgroup stable under a Steinberg endomorphism, the
regular universal property of the quotient descends the endomorphism.  The
quotient Lang map has dense range: the ambient Lang map contains a nonempty
open subset by the finite-fiber theorem, hence is dense, and its composite
with the point-surjective quotient is dense.  Equivariance places that
composite in the quotient Lang range.  The converse open-range theorem then
makes the quotient fixed-point subtype finite.

The quotient constructor takes finite generation of the full right-invariant
coordinate ring explicitly.  Callers can instantiate that hypothesis using
`ClosedSubgroup.rightInvariantCoordinateRing_finiteType`.  The result uses
GLS3, Chapter 2, Theorem 2.1.3 (Steinberg, Theorem 10.3).
-/

namespace Theory.AlgebraicGroup

universe u

set_option linter.style.haveILetI false

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A Steinberg endomorphism descends to a Steinberg endomorphism of a
sigma-stable quotient. -/
public theorem steinbergEndomorphism_invariantQuotient_exists
    {K : Variety k} [AlgebraicGroup K]
    (sigma : AlgebraicGroup.Morphism K K)
    (hsigma : IsAlgebraicSteinbergEndomorphism sigma)
    (hK : Variety.IsConnected K)
    (H : ClosedSubgroup K) (hN : H.toSubgroup.Normal)
    (hstable : forall x : Variety.Point H.carrierVariety,
      sigma.onPoints (H.inclusion.onPoints x) ∈ H.toSubgroup)
    [Algebra.FiniteType k (AlgebraicGroup.rightInvariantCoordinateRing H)] :
    exists (Q : Variety k) (_ : AlgebraicGroup Q)
      (pi : AlgebraicGroup.Morphism K Q)
      (tau : AlgebraicGroup.Morphism Q Q),
      Function.Surjective pi.onPoints /\ pi.kernel = H.toSubgroup /\
      (forall x, pi.onPoints (sigma.onPoints x) = tau.onPoints (pi.onPoints x)) /\
      IsAlgebraicSteinbergEndomorphism tau := by
  obtain ⟨Q, hQalg, pi, hpisurj, hpiker, hpiuniv⟩ :=
    H.quotient_exists_of_finiteType_rightInvariantCoordinateRing hN
  letI : AlgebraicGroup Q := hQalg
  have hHker : H.toSubgroup <= (pi.comp sigma).kernel := by
    intro x hx
    let xH : Variety.Point H.carrierVariety := H.pointEquiv.symm ⟨x, hx⟩
    have hxH : H.inclusion.onPoints xH = x := by
      change (H.pointEquiv xH).val = x
      simp [xH]
    rw [← hxH]
    change pi.onPoints (sigma.onPoints (H.inclusion.onPoints xH)) = 1
    have hm : sigma.onPoints (H.inclusion.onPoints xH) ∈ pi.kernel := by
      rw [hpiker]
      exact hstable xH
    exact MonoidHom.mem_ker.mp hm
  obtain ⟨tau, htaucomp, _⟩ := hpiuniv (pi.comp sigma) hHker
  have hequiv (x : Variety.Point K) :
      pi.onPoints (sigma.onPoints x) = tau.onPoints (pi.onPoints x) := by
    have h := congrArg (fun f : AlgebraicGroup.Morphism K Q => f.onPoints x) htaucomp
    exact h.symm
  have htausurj : Function.Surjective tau.onPoints := by
    intro y
    obtain ⟨x, rfl⟩ := hpisurj y
    obtain ⟨z, rfl⟩ := hsigma.1 x
    exact ⟨pi.onPoints z, hequiv z |>.symm⟩
  have hQconnected : Variety.IsConnected Q :=
    connected_of_surjective_morphism pi hK hpisurj
  obtain ⟨U, hUopen, hUne, hUrange⟩ :=
    langMorphism_exists_nonempty_open_subset_range sigma hsigma hK
  let hKi := connectedAlgebraicGroup_irreducible K hK
  letI : PreirreducibleSpace (Variety.Point K) := ⟨hKi.2⟩
  have hUdense : Dense U := hUopen.dense hUne
  have hambientDense : DenseRange (langMorphism sigma).toFun :=
    hUdense.mono hUrange
  have hcompDense : DenseRange (pi.onPoints ∘ (langMorphism sigma).toFun) :=
    DenseRange.comp hpisurj.denseRange hambientDense pi.toVariety.continuous
  have hlangCompat (x : Variety.Point K) :
      pi.onPoints ((langMorphism sigma).toFun x) =
        (langMorphism tau).toFun (pi.onPoints x) := by
    change pi.onPoints (x * sigma.onPoints x⁻¹) =
      pi.onPoints x * tau.onPoints (pi.onPoints x)⁻¹
    simp only [map_mul, map_inv]
    exact congrArg (fun z => pi.onPoints x * z⁻¹) (hequiv x)
  have htauDense : DenseRange (langMorphism tau).toFun := by
    apply hcompDense.mono
    rintro _ ⟨x, rfl⟩
    exact ⟨pi.onPoints x, (hlangCompat x).symm⟩
  let hQi := connectedAlgebraicGroup_irreducible Q hQconnected
  letI : PreirreducibleSpace (Variety.Point Q) := ⟨hQi.2⟩
  obtain ⟨V, hVopen, hVne, hVrange⟩ :=
    (langMorphism tau).exists_nonempty_open_subset_range_of_dense htauDense
  have htaufixed : Finite {x : Variety.Point Q | tau.onPoints x = x} :=
    finite_fixed_of_langMorphism_open_range tau hQconnected V hVopen hVne hVrange
  exact ⟨Q, hQalg, pi, tau, hpisurj, hpiker, hequiv, htausurj, htaufixed⟩

end Theory.AlgebraicGroup
