module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Theory.AlgebraicGroup.Irreducible.Basic

universe u

namespace Theory.AlgebraicGroup

section

/-- Finite-dimensional affine space presented by the empty equation set. -/
public abbrev affineSpaceVariety (k : Type u) [Field k]
    (σ : Type u) [Finite σ] : Variety k where
  Coordinates := σ
  finiteCoordinates := inferInstance
  equations := ∅

variable {k : Type u} [Field k]
variable {σ : Type u} [Finite σ]

/-- A coordinate function gives a point of affine space. -/
@[expose]
public def affineSpacePoint (x : σ → k) :
    Variety.Point (affineSpaceVariety k σ) :=
  ⟨x, by simp⟩

/-- A polynomial vanishing on every point of finite-dimensional affine space
is zero. -/
public lemma affineSpaceVariety_vanishingIdeal_eq_bot [Infinite k] :
    vanishingIdeal
      (Set.univ : Set (Variety.Point (affineSpaceVariety k σ))) = ⊥ := by
  ext p
  constructor
  · intro hp
    rw [Ideal.mem_bot]
    apply MvPolynomial.funext
    intro x
    have hx := hp (affineSpacePoint x) (Set.mem_univ _)
    have hval : (affineSpacePoint x).val = x := rfl
    rw [hval] at hx
    simpa [evalPolynomial] using hx
  · intro hp
    rw [Ideal.mem_bot] at hp
    subst p
    exact Ideal.zero_mem _

/-- Finite-dimensional affine space over an algebraically closed field is
connected. -/
public lemma affineSpaceVariety_isConnected [IsAlgClosed k] :
    Variety.IsConnected (affineSpaceVariety k σ) := by
  let : Nonempty (Variety.Point (affineSpaceVariety k σ)) :=
    ⟨affineSpacePoint (fun _ => 0)⟩
  apply coordinateRing_domain_variety_connected
  exact ((Ideal.Quotient.isDomain_iff_prime
    (I := vanishingIdeal
      (Set.univ : Set (Variety.Point (affineSpaceVariety k σ))))).mpr (by
        rw [affineSpaceVariety_vanishingIdeal_eq_bot]
        exact Ideal.isPrime_bot))

end

end Theory.AlgebraicGroup
