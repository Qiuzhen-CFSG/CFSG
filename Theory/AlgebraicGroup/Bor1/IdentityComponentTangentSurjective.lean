module

public import Theory.AlgebraicGroup.Bor1.TangentVanishingIdeal
public import Theory.AlgebraicGroup.Morphism.ClosedImage
public import Theory.AlgebraicGroup.Variety.Clopen

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Inclusion of the clopen identity component is surjective on identity
tangent spaces. -/
public theorem identityComponent_inclusion_tangent_surjective
    (G : Variety k) [AlgebraicGroup G] :
    let H := AlgebraicGroup.identityComponentClosedSubgroup G
    Function.Surjective
      (identityTangentMorphismLinearMap H.inclusion) := by
  dsimp only
  let H := AlgebraicGroup.identityComponentClosedSubgroup G
  let C := AlgebraicGroup.identityComponent G
  have hCclopen : IsClopen C :=
    ⟨Variety.isClosed_iff_isZariskiClosed.mpr
      (AlgebraicGroup.identityComponent_isClosed G),
      AlgebraicGroup.identityComponent_isOpen G⟩
  obtain ⟨p, hpOne, hpZero⟩ :=
    exists_polynomial_eq_one_on_of_isClopen G C hCclopen
  let e : Variety.PolynomialFunction G :=
    Variety.PolynomialFunction.ofPolynomial G p
  have heOne (x : Variety.Point G) (hx : x ∈ C) : e x = 1 :=
    hpOne x hx
  have heZero (x : Variety.Point G) (hx : x ∉ C) : e x = 0 :=
    hpZero x hx
  intro D
  apply (identityTangent_inclusion_range_iff_vanishingIdeal H D).mpr
  intro f hf
  have hfZero (x : Variety.Point G) (hx : x ∈ C) : f x = 0 := by
    apply (H.mem_vanishingIdeal_iff f).mp hf x
    change x ∈ AlgebraicGroup.identityComponentSubgroup G
    exact hx
  have hfactor : f = (1 - e) * f := by
    apply Variety.PolynomialFunction.ext
    intro x
    by_cases hx : x ∈ C
    · change f x = (1 - e x) * f x
      rw [heOne x hx, hfZero x hx]
      simp
    · change f x = (1 - e x) * f x
      rw [heZero x hx]
      simp
  have hfOne : f (1 : Variety.Point G) = 0 :=
    hfZero 1 (AlgebraicGroup.one_mem_identityComponent G)
  have heAtOne : e (1 : Variety.Point G) = 1 :=
    heOne 1 (AlgebraicGroup.one_mem_identityComponent G)
  rw [hfactor, D.leibniz]
  change (1 - e (1 : Variety.Point G)) * D f +
    f (1 : Variety.Point G) * D (1 - e) = 0
  rw [heAtOne, hfOne]
  simp

end Theory.AlgebraicGroup.Bor1
