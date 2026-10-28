module

public import Theory.AlgebraicGroup.CoordinateRing.Hopf.Flatness

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Pullback by left translation carries the complement of the point ideal
at `a` onto the complement of the identity point ideal. -/
public theorem leftTranslateAlgEquiv_map_pointPrime_primeCompl
    (V : Variety k) [AlgebraicGroup V] (a : Variety.Point V) :
    Submonoid.map (leftTranslateAlgEquiv V a).toMonoidHom
        (V.pointPrime a).asIdeal.primeCompl =
      (V.pointPrime 1).asIdeal.primeCompl := by
  apply le_antisymm
  · rintro y ⟨r, hr, rfl⟩
    change leftTranslateAlgEquiv V a r ∉ (V.pointPrime 1).asIdeal
    intro hy
    apply hr
    change r a = 0
    change r ((AlgebraicGroup.leftMulMorphism V a).toFun 1) = 0 at hy
    rw [AlgebraicGroup.leftMulMorphism_apply, mul_one] at hy
    exact hy
  · intro y hy
    refine ⟨(leftTranslateAlgEquiv V a).symm y, ?_, ?_⟩
    · change (leftTranslateAlgEquiv V a).symm y ∉
        (V.pointPrime a).asIdeal
      intro h
      apply hy
      change y 1 = 0
      change y ((AlgebraicGroup.leftMulMorphism V a⁻¹).toFun a) = 0 at h
      simpa [AlgebraicGroup.leftMulMorphism_apply] using h
    · exact (leftTranslateAlgEquiv V a).apply_symm_apply y

end Theory.AlgebraicGroup.Bor1
