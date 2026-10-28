module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Smooth.Locus
public import Theory.AlgebraicGroup.Bor1.AugmentedCotangentKaehler
public import Theory.AlgebraicGroup.Bor1.AugmentedLocalizationResidue
public import Theory.AlgebraicGroup.Bor1.FormallySmoothTransitivity
public import Theory.AlgebraicGroup.Bor1.MaximalCotangentLocalizationInjective

universe u

open scoped TensorProduct

namespace Theory.AlgebraicGroup.Bor1

open IsLocalRing

set_option linter.style.haveILetI false in
/-- An injective map on augmented cotangent spaces makes the corresponding
localization formally smooth. -/
public theorem smoothAt_of_augmentedCotangentMap_injective
    {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Algebra.EssFiniteType k A] [Algebra.EssFiniteType k B]
    [Algebra.FormallySmooth k A] [Algebra.FormallySmooth k B]
    (eA : A →ₐ[k] k) (eB : B →ₐ[k] k)
    [(RingHom.ker eB).IsMaximal]
    (heA : Function.Surjective eA) (heB : Function.Surjective eB)
    (hcomm : eB.comp (IsScalarTower.toAlgHom k A B) = eA)
    (hcot : Function.Injective
      (Ideal.mapCotangent (RingHom.ker eA) (RingHom.ker eB)
        (IsScalarTower.toAlgHom k A B) (by
          intro x hx
          change (eB.comp (IsScalarTower.toAlgHom k A B)) x = 0
          rw [hcomm]
          exact hx))) :
    Algebra.IsSmoothAt A (RingHom.ker eB) := by
  let m := RingHom.ker eB
  letI : m.IsMaximal := inferInstance
  letI : m.IsPrime := inferInstance
  let T := Localization.AtPrime m
  change Algebra.FormallySmooth A T
  apply formallySmooth_of_split_mapBaseChange (R := k) (S := A) (T := T)
  letI : Module.Free T Ω[T⁄k] := Module.free_of_flat_of_isLocalRing
  apply (IsLocalRing.split_injective_iff_lTensor_residueField_injective
    (KaehlerDifferential.mapBaseChange k A T)).mpr
  let K := IsLocalRing.ResidueField T
  let eK : K ≃ₐ[k] k := augmentedLocalizationResidueAlgEquiv eB heB
  have eK_algebraMap (a : A) : eK (algebraMap A K a) = eA a := by
    rw [IsScalarTower.algebraMap_apply A B K]
    calc
      eK (algebraMap B K (algebraMap A B a)) =
          eB (algebraMap A B a) := by
        exact augmentedLocalizationResidueAlgEquiv_algebraMap eB heB _
      _ = eA a := DFunLike.congr_fun hcomm a
  letI : Algebra A k := eA.toRingHom.toAlgebra
  let eKA : K ≃ₗ[A] k := {
    toFun := eK
    invFun := eK.symm
    left_inv := eK.symm_apply_apply
    right_inv := eK.apply_symm_apply
    map_add' := map_add eK
    map_smul' := by
      intro a x
      simp only [Algebra.smul_def]
      rw [map_mul, eK_algebraMap]
      rfl }
  let sourceCoeffEquiv : K ⊗[A] Ω[A⁄k] ≃ₗ[A] k ⊗[A] Ω[A⁄k] :=
    TensorProduct.AlgebraTensorModule.congr eKA (LinearEquiv.refl A Ω[A⁄k])
  let augA := augmentedCotangentKaehlerEquiv eA heA
  have haugA (x : RingHom.ker eA) :
      augA ((RingHom.ker eA).toCotangent x) =
        (1 : k) ⊗ₜ[A] KaehlerDifferential.D k A x.1 := by
    rfl
  let residueAlgHom : T →ₐ[k] K := Ideal.Quotient.mkₐ k (maximalIdeal T)
  let eT : T →ₐ[k] k := eK.toAlgHom.comp residueAlgHom
  have heT : Function.Surjective eT :=
    eK.surjective.comp (Ideal.Quotient.mk_surjective :
      Function.Surjective (Ideal.Quotient.mk (maximalIdeal T)))
  have hkerT : RingHom.ker eT = maximalIdeal T := by
    change RingHom.ker (eK.toRingHom.comp residueAlgHom.toRingHom) =
      maximalIdeal T
    rw [RingHom.ker_comp_of_injective residueAlgHom.toRingHom
      (f := eK.toRingEquiv.toRingHom) eK.injective]
    exact Ideal.mk_ker
  letI : Algebra T k := eT.toRingHom.toAlgebra
  let eKT : K ≃ₗ[T] k := {
    toFun := eK
    invFun := eK.symm
    left_inv := eK.symm_apply_apply
    right_inv := eK.apply_symm_apply
    map_add' := map_add eK
    map_smul' := by
      intro t x
      simp only [Algebra.smul_def]
      rw [map_mul]
      rfl }
  let targetCoeffEquiv : K ⊗[T] Ω[T⁄k] ≃ₗ[T] k ⊗[T] Ω[T⁄k] :=
    TensorProduct.AlgebraTensorModule.congr eKT (LinearEquiv.refl T Ω[T⁄k])
  let augT := augmentedCotangentKaehlerEquiv eT heT
  have haugT (x : RingHom.ker eT) :
      augT ((RingHom.ker eT).toCotangent x) =
        (1 : k) ⊗ₜ[T] KaehlerDifferential.D k T x.1 := by
    rfl
  let cancelSource : K ⊗[T] (T ⊗[A] Ω[A⁄k]) ≃ₗ[k] K ⊗[A] Ω[A⁄k] :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      A T K K Ω[A⁄k]).restrictScalars k
  let sourceEquiv : K ⊗[T] (T ⊗[A] Ω[A⁄k]) ≃ₗ[k]
      (RingHom.ker eA).Cotangent :=
    cancelSource ≪≫ₗ sourceCoeffEquiv.restrictScalars k ≪≫ₗ augA.symm
  let targetEquiv : K ⊗[T] Ω[T⁄k] ≃ₗ[k] (maximalIdeal T).Cotangent :=
    targetCoeffEquiv.restrictScalars k ≪≫ₗ augT.symm ≪≫ₗ
      (Ideal.Cotangent.equivOfEq (RingHom.ker eT)
        (maximalIdeal T) hkerT).restrictScalars k
  have hcomp : RingHom.ker eB ≤
      (maximalIdeal T).comap (Algebra.ofId B T) := by
    change RingHom.ker eB ≤ (maximalIdeal T).comap (algebraMap B T)
    rw [← Ideal.under_def,
      IsLocalization.AtPrime.under_maximalIdeal T (RingHom.ker eB)]
  let cotMap : (RingHom.ker eA).Cotangent →ₗ[k]
      (RingHom.ker eB).Cotangent :=
    Ideal.mapCotangent (RingHom.ker eA) (RingHom.ker eB)
      (IsScalarTower.toAlgHom k A B) (by
        intro x hx
        change (eB.comp (IsScalarTower.toAlgHom k A B)) x = 0
        rw [hcomm]
        exact hx)
  let localCotMap : (RingHom.ker eB).Cotangent →ₗ[k]
      (maximalIdeal T).Cotangent :=
    (Ideal.mapCotangent (RingHom.ker eB) (maximalIdeal T)
      (Algebra.ofId B T) hcomp).restrictScalars k
  have hdiagram : targetEquiv.toLinearMap.comp
        ((LinearMap.lTensor K
          (KaehlerDifferential.mapBaseChange k A T)).restrictScalars k) =
      (localCotMap.comp cotMap).comp sourceEquiv.toLinearMap := by
    ext z
    obtain ⟨x, hx⟩ :=
      (RingHom.ker eA).toCotangent_surjective (sourceEquiv z)
    have hz : z = sourceEquiv.symm
        ((RingHom.ker eA).toCotangent x) := by
      apply sourceEquiv.injective
      simpa using hx.symm
    subst z
    simp only [LinearMap.comp_apply]
    change targetEquiv
        ((LinearMap.lTensor K (KaehlerDifferential.mapBaseChange k A T))
          (sourceEquiv.symm ((RingHom.ker eA).toCotangent x))) =
      localCotMap (cotMap
        (sourceEquiv (sourceEquiv.symm ((RingHom.ker eA).toCotangent x))))
    rw [sourceEquiv.apply_symm_apply]
    have hsource : sourceEquiv.symm ((RingHom.ker eA).toCotangent x) =
        (1 : K) ⊗ₜ[T]
          ((1 : T) ⊗ₜ[A] KaehlerDifferential.D k A x.1) := by
      apply sourceEquiv.injective
      rw [sourceEquiv.apply_symm_apply]
      simp [sourceEquiv, cancelSource, sourceCoeffEquiv, eKA]
      rw [augA.eq_symm_apply]
      exact haugA x
    rw [hsource]
    have hxT : eT (algebraMap A T x.1) = 0 := by
      change eK (algebraMap T K (algebraMap A T x.1)) = 0
      rw [← IsScalarTower.algebraMap_apply A T K, eK_algebraMap]
      exact x.2
    let xT : RingHom.ker eT := ⟨algebraMap A T x.1, hxT⟩
    have haugTinv : augT.symm
        ((1 : k) ⊗ₜ[T]
          KaehlerDifferential.D k T (algebraMap A T x.1)) =
        (RingHom.ker eT).toCotangent xT := by
      rw [augT.symm_apply_eq]
      exact (haugT xT).symm
    simp [targetEquiv, targetCoeffEquiv, eKT, cotMap, localCotMap]
    rw [haugTinv]
    simp only [Ideal.Cotangent.equivOfEq_toCotangent]
    apply congrArg (Ideal.toCotangent (maximalIdeal T))
    apply Subtype.ext
    rfl
  intro x y hxy
  apply sourceEquiv.injective
  apply hcot
  apply maximalCotangentLocalizationMap_injective
    B (RingHom.ker eB) T hcomp
  change ((localCotMap.comp cotMap).comp sourceEquiv.toLinearMap) x =
    ((localCotMap.comp cotMap).comp sourceEquiv.toLinearMap) y
  rw [← hdiagram, LinearMap.comp_apply, LinearMap.comp_apply]
  exact congrArg targetEquiv hxy

end Theory.AlgebraicGroup.Bor1
