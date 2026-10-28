module

public import Mathlib.RingTheory.RingHom.Smooth
public import Theory.AlgebraicGroup.Bor1.IdentitySmoothness
public import Theory.AlgebraicGroup.Bor1.LeftTranslateLocalization

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]

set_option linter.style.haveILetI false in
/-- Surjectivity of the identity differential makes a morphism of algebraic
groups smooth at every rational point of its source. -/
public theorem point_isSmoothAt_of_tangent_surjective
    (f : AlgebraicGroup.Morphism G Q)
    (hdf : Function.Surjective (identityTangentMorphismLinearMap f))
    (x : Variety.Point G) :
    letI : Algebra (Variety.PolynomialFunction Q)
        (Variety.PolynomialFunction G) :=
      f.toVariety.pullbackAlgHom.toRingHom.toAlgebra
    Algebra.IsSmoothAt (Variety.PolynomialFunction Q)
      (G.pointPrime x).asIdeal := by
  let A := Variety.PolynomialFunction Q
  let B := Variety.PolynomialFunction G
  let F := f.toVariety.pullbackAlgHom
  letI : Algebra A B := F.toRingHom.toAlgebra
  letI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun r =>
    (F.commutes r).symm
  have h1 : Algebra.IsSmoothAt A (G.pointPrime 1).asIdeal :=
    identity_isSmoothAt_of_tangent_surjective f hdf
  let a := f.onPoints x
  let eA := leftTranslateAlgEquiv Q a
  let eB := leftTranslateAlgEquiv G x
  have hcomm : eB.toRingEquiv.toRingHom.comp F.toRingHom =
      F.toRingHom.comp eA.toRingEquiv.toRingHom := by
    apply RingHom.ext
    intro q
    apply Variety.PolynomialFunction.ext
    intro y
    change q (f.onPoints (x * y)) = q (a * f.onPoints y)
    rw [f.onPoints.map_mul]
  let mX := (G.pointPrime x).asIdeal
  let m1 := (G.pointPrime 1).asIdeal
  let eBloc : Localization.AtPrime mX ≃+* Localization.AtPrime m1 :=
    IsLocalization.ringEquivOfRingEquiv _ _ eB.toRingEquiv
      (leftTranslateAlgEquiv_map_pointPrime_primeCompl G x)
  have hlocalcomm : eBloc.toRingHom.comp
        (algebraMap A (Localization.AtPrime mX)) =
      (algebraMap A (Localization.AtPrime m1)).comp
        eA.toRingEquiv.toRingHom := by
    apply RingHom.ext
    intro q
    change eBloc (algebraMap B (Localization.AtPrime mX) (F q)) =
      algebraMap B (Localization.AtPrime m1) (F (eA q))
    dsimp [eBloc]
    rw [IsLocalization.ringEquivOfRingEquiv_eq
      (M := mX.primeCompl) (T := m1.primeCompl)
      (S := Localization.AtPrime mX) (Q := Localization.AtPrime m1)
      (j := eB.toRingEquiv)
      (leftTranslateAlgEquiv_map_pointPrime_primeCompl G x)]
    exact congrArg (algebraMap B (Localization.AtPrime m1))
      (DFunLike.congr_fun hcomm q)
  have h1rh : RingHom.FormallySmooth
      (algebraMap A (Localization.AtPrime m1)) :=
    RingHom.formallySmooth_algebraMap.mpr h1
  have hpre : RingHom.FormallySmooth
      ((algebraMap A (Localization.AtPrime m1)).comp
        eA.toRingEquiv.toRingHom) :=
    RingHom.FormallySmooth.respectsIso.2 _ eA.toRingEquiv h1rh
  have hpost : RingHom.FormallySmooth
      (eBloc.toRingHom.comp (algebraMap A (Localization.AtPrime mX))) := by
    rw [hlocalcomm]
    exact hpre
  have hx' := RingHom.FormallySmooth.respectsIso.1 _ eBloc.symm hpost
  have hxrh : RingHom.FormallySmooth
      (algebraMap A (Localization.AtPrime mX)) := by
    convert hx' using 1
    ext q
    simp
  exact RingHom.formallySmooth_algebraMap.mp hxrh

end Theory.AlgebraicGroup.Bor1
