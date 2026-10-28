module

public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Kähler differentials of a commutative Hopf algebra

For a commutative Hopf algebra `A` over a field `k`, this module identifies
`Ω[A⁄k]` with the scalar extension to `A` of the cotangent space at the
counit.  In particular, the module of Kähler differentials is free over `A`;
no finite-type or reducedness hypothesis is required.

Write `I = ker ε`.  The forward map is induced by the derivation
`a ↦ ∑ a₁ ⊗ [a₂ - ε(a₂)]`.  Its inverse sends a cotangent class to the
corresponding invariant differential
`∑ S(a₁) · d(a₂)`.  Coassociativity and the two antipode identities prove
that these maps are inverse.  Since `I / I²` is a vector space over `k`,
its scalar extension is a free `A`-module.

This is the affine-algebra form of the translation argument in the Stacks
Project, Lemma 39.6.3 (tag 047I).
-/

open scoped TensorProduct
open Coalgebra

universe u v

namespace Theory.AlgebraicGroup

variable (k : Type u) (A : Type v) [Field k] [CommRing A] [HopfAlgebra k A]

private abbrev augIdeal : Ideal A := RingHom.ker (Bialgebra.counitAlgHom k A).toRingHom

private abbrev augCotangent := (augIdeal k A).Cotangent

private noncomputable def augmentationDifference : A →ₗ[k] augCotangent k A :=
  ((augIdeal k A).toCotangent.restrictScalars k).comp <|
    LinearMap.codRestrict ((augIdeal k A).restrictScalars k)
      (LinearMap.id - (Algebra.linearMap k A).comp (Coalgebra.counit (R := k))) (fun a ↦ by
        change a - algebraMap k A (Coalgebra.counit a) ∈ augIdeal k A
        rw [RingHom.mem_ker]
        simp)

private lemma augmentationDifference_apply (a : A) :
    augmentationDifference k A a =
      (augIdeal k A).toCotangent
        ⟨a - algebraMap k A (Coalgebra.counit a), by
          rw [RingHom.mem_ker]
          simp⟩ :=
  rfl

private lemma augmentationDifference_mem (x : augIdeal k A) :
    augmentationDifference k A x = (augIdeal k A).toCotangent x := by
  rw [augmentationDifference_apply, Ideal.toCotangent_eq]
  change (x : A) - algebraMap k A (Coalgebra.counit (x : A)) - x ∈ (augIdeal k A) ^ 2
  rw [show Coalgebra.counit (R := k) (x : A) = 0 by exact x.property]
  simp

private lemma augmentationDifference_mul (a b : A) :
    augmentationDifference k A (a * b) =
      Coalgebra.counit (R := k) a • augmentationDifference k A b +
        Coalgebra.counit (R := k) b • augmentationDifference k A a := by
  rw [augmentationDifference_apply, augmentationDifference_apply,
    augmentationDifference_apply, ← LinearMap.map_smul_of_tower,
    ← LinearMap.map_smul_of_tower, ← map_add,
    Ideal.toCotangent_eq]
  simp only [Submodule.coe_add, Bialgebra.counit_mul, map_mul]
  have ha : a - algebraMap k A (Coalgebra.counit a) ∈ augIdeal k A := by
    rw [RingHom.mem_ker]
    simp
  have hb : b - algebraMap k A (Coalgebra.counit b) ∈ augIdeal k A := by
    rw [RingHom.mem_ker]
    simp
  have hsmul (r : k) (x : augIdeal k A) : ((r • x : augIdeal k A) : A) = r • (x : A) :=
    rfl
  have heq :
      a * b - algebraMap k A (Coalgebra.counit (R := k) a) *
          algebraMap k A (Coalgebra.counit (R := k) b) -
          ((Coalgebra.counit (R := k) a •
            (⟨b - algebraMap k A (Coalgebra.counit (R := k) b), hb⟩ : augIdeal k A) :
              augIdeal k A) : A) -
          ((Coalgebra.counit (R := k) b •
            (⟨a - algebraMap k A (Coalgebra.counit (R := k) a), ha⟩ : augIdeal k A) :
              augIdeal k A) : A) =
        (a - algebraMap k A (Coalgebra.counit (R := k) a)) *
          (b - algebraMap k A (Coalgebra.counit (R := k) b)) := by
    rw [hsmul, hsmul]
    simp only [Algebra.smul_def]
    ring
  rw [sub_add_eq_sub_sub, heq]
  rw [pow_two]
  exact Ideal.mul_mem_mul ha hb

private lemma sum_smul_counit {a : A} {ι : Type*} (r : Coalgebra.Repr k a ι) :
    ∑ i ∈ r.index, Coalgebra.counit (R := k) (r.right i) • r.left i = a := by
  have h := Coalgebra.sum_tmul_counit_eq r
  apply_fun (TensorProduct.rid k A) at h
  simpa only [map_sum, TensorProduct.rid_tmul, one_smul] using h

private lemma sum_smul_mul_tmul {a : A} {ι : Type*} (r : Coalgebra.Repr k a ι)
    (b : A) (m : augCotangent k A) :
    ∑ i ∈ r.index,
        (Coalgebra.counit (R := k) (r.right i) • (r.left i * b)) ⊗ₜ[k] m =
      (a * b) ⊗ₜ[k] m := by
  rw [← TensorProduct.sum_tmul]
  congr 1
  simp_rw [← smul_mul_assoc]
  rw [← Finset.sum_mul]
  rw [sum_smul_counit]

private noncomputable def cotangentDerivationLinear :
    A →ₗ[k] A ⊗[k] augCotangent k A :=
  (TensorProduct.map LinearMap.id (augmentationDifference k A)).comp Coalgebra.comul

private lemma cotangentDerivationLinear_apply (a : A) :
    cotangentDerivationLinear k A a =
      TensorProduct.map LinearMap.id (augmentationDifference k A) (Coalgebra.comul a) :=
  rfl

private noncomputable def cotangentDerivation :
    Derivation k A (A ⊗[k] augCotangent k A) where
  toLinearMap := cotangentDerivationLinear k A
  map_one_eq_zero' := by
    have h : augmentationDifference k A (1 : A) = 0 := by
      rw [augmentationDifference_apply]
      rw [Ideal.toCotangent_eq_zero]
      simp
    rw [cotangentDerivationLinear_apply, Bialgebra.comul_one,
      Algebra.TensorProduct.one_def, TensorProduct.map_tmul, h,
      TensorProduct.tmul_zero]
  leibniz' := fun a b ↦ by
    let ra := ℛ k a
    let rb := ℛ k b
    simp only [cotangentDerivationLinear_apply, Bialgebra.comul_mul,
      ← ra.eq, ← rb.eq, Finset.sum_mul_sum, map_sum, TensorProduct.map_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, augmentationDifference_mul,
      TensorProduct.tmul_add, TensorProduct.tmul_smul, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [LinearMap.id_coe, id_eq, TensorProduct.smul_tmul', smul_eq_mul] using
        sum_smul_mul_tmul k A ra (rb.left i) (augmentationDifference k A (rb.right i))
    · rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [LinearMap.id_coe, id_eq, mul_comm, TensorProduct.smul_tmul', smul_eq_mul] using
        sum_smul_mul_tmul k A rb (ra.left i) (augmentationDifference k A (ra.right i))

private lemma cotangentDerivation_apply_repr {a : A} {ι : Type*} (r : Coalgebra.Repr k a ι) :
    cotangentDerivation k A a =
      ∑ i ∈ r.index, r.left i ⊗ₜ[k] augmentationDifference k A (r.right i) := by
  change TensorProduct.map LinearMap.id (augmentationDifference k A) (Coalgebra.comul a) = _
  rw [← r.eq]
  simp

private noncomputable def leftMultiplyDifferential :
    A →ₗ[A] A →ₗ[k] Ω[A⁄k] where
  toFun a := a • (KaehlerDifferential.D k A).toLinearMap
  map_add' a b := by ext; simp [add_smul]
  map_smul' a b := by ext; simp [mul_smul]

private noncomputable def invariantDifferentialRaw : A →ₗ[k] Ω[A⁄k] :=
  ((TensorProduct.AlgebraTensorModule.lift
      (leftMultiplyDifferential k A)).restrictScalars k).comp
    ((TensorProduct.map (HopfAlgebra.antipode k) LinearMap.id).comp Coalgebra.comul)

private lemma invariantDifferentialRaw_apply_repr {a : A} {ι : Type*} (r : Coalgebra.Repr k a ι) :
    invariantDifferentialRaw k A a =
      ∑ i ∈ r.index, HopfAlgebra.antipode k (r.left i) •
        KaehlerDifferential.D k A (r.right i) := by
  change (TensorProduct.AlgebraTensorModule.lift (leftMultiplyDifferential k A))
    (TensorProduct.map (HopfAlgebra.antipode k) LinearMap.id (Coalgebra.comul a)) = _
  rw [← r.eq]
  simp [leftMultiplyDifferential]

private lemma sum_antipode_smul_right {a : A} {ι : Type*} (r : Coalgebra.Repr k a ι)
    (m : Ω[A⁄k]) :
    ∑ i ∈ r.index, HopfAlgebra.antipode k (r.left i) • r.right i • m =
      Coalgebra.counit (R := k) a • m := by
  simp_rw [smul_smul]
  rw [← Finset.sum_smul, HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit]
  simp

private lemma invariantDifferentialRaw_mul (a b : A) :
    invariantDifferentialRaw k A (a * b) =
      Coalgebra.counit (R := k) a • invariantDifferentialRaw k A b +
        Coalgebra.counit (R := k) b • invariantDifferentialRaw k A a := by
  let ra := ℛ k a
  let rb := ℛ k b
  rw [invariantDifferentialRaw_apply_repr k A (ra.mul rb),
    invariantDifferentialRaw_apply_repr k A ra,
    invariantDifferentialRaw_apply_repr k A rb]
  simp only [Coalgebra.Repr.mul_index, Coalgebra.Repr.mul_left,
    Coalgebra.Repr.mul_right, Finset.sum_product, HopfAlgebra.antipode_mul_distrib,
    Derivation.leibniz, smul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
      sum_antipode_smul_right k A ra
        (HopfAlgebra.antipode k (rb.left i) • KaehlerDifferential.D k A (rb.right i))
  · rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
      sum_antipode_smul_right k A rb
        (HopfAlgebra.antipode k (ra.left i) • KaehlerDifferential.D k A (ra.right i))

private lemma invariantDifferentialRaw_one : invariantDifferentialRaw k A 1 = 0 := by
  change (TensorProduct.AlgebraTensorModule.lift (leftMultiplyDifferential k A))
    (TensorProduct.map (HopfAlgebra.antipode k) LinearMap.id (Coalgebra.comul 1)) = 0
  rw [Bialgebra.comul_one, Algebra.TensorProduct.one_def, TensorProduct.map_tmul,
    TensorProduct.AlgebraTensorModule.lift_tmul]
  simp [leftMultiplyDifferential]

private lemma invariantDifferentialRaw_algebraMap (r : k) :
    invariantDifferentialRaw k A (algebraMap k A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, invariantDifferentialRaw_one, smul_zero]

private noncomputable def invariantDifferentialOnIdeal :
    augIdeal k A →ₗ[k] Ω[A⁄k] :=
  (invariantDifferentialRaw k A).comp ((augIdeal k A).subtype.restrictScalars k)

private lemma invariantDifferentialOnIdeal_mul (x y : augIdeal k A) :
    invariantDifferentialOnIdeal k A (x * y) = 0 := by
  change invariantDifferentialRaw k A ((x : A) * (y : A)) = 0
  rw [invariantDifferentialRaw_mul]
  have hx : Coalgebra.counit (R := k) (x : A) = 0 := x.property
  have hy : Coalgebra.counit (R := k) (y : A) = 0 := y.property
  rw [hx, hy, zero_smul, zero_smul, zero_add]

private noncomputable def invariantCotangent : augCotangent k A →ₗ[k] Ω[A⁄k] :=
  Ideal.Cotangent.lift (invariantDifferentialOnIdeal k A)
    (invariantDifferentialOnIdeal_mul k A)

private lemma invariantCotangent_augmentationDifference (a : A) :
    invariantCotangent k A (augmentationDifference k A a) =
      invariantDifferentialRaw k A a := by
  rw [augmentationDifference_apply, invariantCotangent,
    Ideal.Cotangent.lift_toCotangent, invariantDifferentialOnIdeal,
    LinearMap.comp_apply]
  change invariantDifferentialRaw k A
      (a - algebraMap k A (Coalgebra.counit (R := k) a)) =
    invariantDifferentialRaw k A a
  rw [map_sub, invariantDifferentialRaw_algebraMap, sub_zero]

private noncomputable def cotangentToDifferential :
    A ⊗[k] augCotangent k A →ₗ[A] Ω[A⁄k] :=
  LinearMap.liftBaseChange A (invariantCotangent k A)

private noncomputable def differentialToCotangent :
    Ω[A⁄k] →ₗ[A] A ⊗[k] augCotangent k A :=
  (cotangentDerivation k A).liftKaehlerDifferential

private noncomputable def antipodeScaledDifferential (a : A) :
    A →ₗ[k] A →ₗ[k] Ω[A⁄k] where
  toFun b := (a * HopfAlgebra.antipode k b) • (KaehlerDifferential.D k A).toLinearMap
  map_add' b c := by ext; simp [mul_add, add_smul]
  map_smul' r b := by
    ext c
    simp only [map_smul, RingHom.id_apply, LinearMap.smul_apply]
    rw [← IsScalarTower.smul_assoc]
    congr 1
    simp [Algebra.smul_def, mul_left_comm]

private noncomputable def tripleDifferentialLeft :
    A →ₗ[k] (A ⊗[k] A) →ₗ[k] Ω[A⁄k] where
  toFun a := TensorProduct.lift (antipodeScaledDifferential k A a)
  map_add' a b := by
    ext c d
    simp [antipodeScaledDifferential, add_mul, add_smul]
  map_smul' r a := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul b c =>
      simp only [LinearMap.smul_apply, RingHom.id_apply, TensorProduct.lift.tmul]
      change ((r • a) * HopfAlgebra.antipode k b) • KaehlerDifferential.D k A c =
        r • ((a * HopfAlgebra.antipode k b) • KaehlerDifferential.D k A c)
      rw [← IsScalarTower.smul_assoc]
      congr 1
      simp [Algebra.smul_def, mul_assoc]

private noncomputable def tripleDifferential :
    A ⊗[k] (A ⊗[k] A) →ₗ[k] Ω[A⁄k] :=
  TensorProduct.lift (tripleDifferentialLeft k A)

private lemma tripleDifferential_tmul (a b c : A) :
    tripleDifferential k A (a ⊗ₜ[k] (b ⊗ₜ[k] c)) =
      (a * HopfAlgebra.antipode k b) • KaehlerDifferential.D k A c := by
  simp [tripleDifferential, tripleDifferentialLeft, antipodeScaledDifferential]

private lemma coassoc_tripleDifferential (a : A) :
    let r := ℛ k a
    let rr := fun i ↦ ℛ k (r.right i)
    let rl := fun i ↦ ℛ k (r.left i)
    ∑ i ∈ r.index, ∑ j ∈ (rr i).index,
        (r.left i * HopfAlgebra.antipode k ((rr i).left j)) •
          KaehlerDifferential.D k A ((rr i).right j) =
      ∑ i ∈ r.index, ∑ j ∈ (rl i).index,
        ((rl i).left j * HopfAlgebra.antipode k ((rl i).right j)) •
          KaehlerDifferential.D k A (r.right i) := by
  dsimp only
  let r := ℛ k a
  let rr := fun i ↦ ℛ k (r.right i)
  let rl := fun i ↦ ℛ k (r.left i)
  have h := (Coalgebra.sum_tmul_tmul_eq r rl rr).symm
  apply_fun tripleDifferential k A at h
  simpa only [map_sum, tripleDifferential_tmul] using h

private lemma sum_smul_antipode_right {a : A} {ι : Type*} (r : Coalgebra.Repr k a ι)
    (m : Ω[A⁄k]) :
    ∑ i ∈ r.index, r.left i • HopfAlgebra.antipode k (r.right i) • m =
      Coalgebra.counit (R := k) a • m := by
  simp_rw [smul_smul]
  rw [← Finset.sum_smul, HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit]
  simp

private lemma sum_counit_smul_differential {a : A} {ι : Type*}
    (r : Coalgebra.Repr k a ι) :
    ∑ i ∈ r.index, Coalgebra.counit (R := k) (r.left i) •
        KaehlerDifferential.D k A (r.right i) =
      KaehlerDifferential.D k A a := by
  have h := Coalgebra.sum_counit_smul r
  apply_fun KaehlerDifferential.D k A at h
  rw [map_sum] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i hi
  exact ((KaehlerDifferential.D k A).toLinearMap.map_smul _ _).symm

private lemma cotangentToDifferential_cotangentDerivation (a : A) :
    cotangentToDifferential k A (cotangentDerivation k A a) =
      KaehlerDifferential.D k A a := by
  let r := ℛ k a
  let rr := fun i ↦ ℛ k (r.right i)
  let rl := fun i ↦ ℛ k (r.left i)
  change cotangentToDifferential k A
    (TensorProduct.map LinearMap.id (augmentationDifference k A) (Coalgebra.comul a)) = _
  rw [← r.eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
    LinearMap.liftBaseChange_tmul, cotangentToDifferential,
    invariantCotangent_augmentationDifference]
  simp_rw [invariantDifferentialRaw_apply_repr k A (rr _)]
  simp only [Finset.smul_sum, smul_smul]
  rw [coassoc_tripleDifferential]
  calc
    _ = ∑ i ∈ r.index, Coalgebra.counit (R := k) (r.left i) •
          KaehlerDifferential.D k A (r.right i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [smul_smul] using
        sum_smul_antipode_right k A (rl i) (KaehlerDifferential.D k A (r.right i))
    _ = _ := sum_counit_smul_differential k A r

private lemma cotangentToDifferential_comp_differentialToCotangent :
    (cotangentToDifferential k A).comp (differentialToCotangent k A) = LinearMap.id := by
  apply Derivation.liftKaehlerDifferential_unique
  ext a
  change cotangentToDifferential k A
    (differentialToCotangent k A (KaehlerDifferential.D k A a)) =
      KaehlerDifferential.D k A a
  rw [differentialToCotangent, Derivation.liftKaehlerDifferential_comp_D]
  exact cotangentToDifferential_cotangentDerivation k A a

private noncomputable def tripleCotangent :
    A ⊗[k] (A ⊗[k] A) →ₗ[k] A ⊗[k] augCotangent k A :=
  (TensorProduct.map (LinearMap.mul' k A) (augmentationDifference k A)).comp
    ((TensorProduct.assoc k A A A).symm.toLinearMap.comp
      (TensorProduct.map (HopfAlgebra.antipode k)
        (TensorProduct.map LinearMap.id LinearMap.id)))

private lemma tripleCotangent_tmul (a b c : A) :
    tripleCotangent k A (a ⊗ₜ[k] (b ⊗ₜ[k] c)) =
      (HopfAlgebra.antipode k a * b) ⊗ₜ[k] augmentationDifference k A c := by
  simp [tripleCotangent]

private lemma coassoc_tripleCotangent (a : A) :
    let r := ℛ k a
    let rr := fun i ↦ ℛ k (r.right i)
    let rl := fun i ↦ ℛ k (r.left i)
    ∑ i ∈ r.index, ∑ j ∈ (rr i).index,
        (HopfAlgebra.antipode k (r.left i) * (rr i).left j) ⊗ₜ[k]
          augmentationDifference k A ((rr i).right j) =
      ∑ i ∈ r.index, ∑ j ∈ (rl i).index,
        (HopfAlgebra.antipode k ((rl i).left j) * (rl i).right j) ⊗ₜ[k]
          augmentationDifference k A (r.right i) := by
  dsimp only
  let r := ℛ k a
  let rr := fun i ↦ ℛ k (r.right i)
  let rl := fun i ↦ ℛ k (r.left i)
  have h := (Coalgebra.sum_tmul_tmul_eq r rl rr).symm
  apply_fun tripleCotangent k A at h
  simpa only [map_sum, tripleCotangent_tmul] using h

private lemma sum_antipode_mul_tmul {a : A} {ι : Type*} (r : Coalgebra.Repr k a ι)
    (m : augCotangent k A) :
    ∑ i ∈ r.index,
        (HopfAlgebra.antipode k (r.left i) * r.right i) ⊗ₜ[k] m =
      algebraMap k A (Coalgebra.counit (R := k) a) ⊗ₜ[k] m := by
  rw [← TensorProduct.sum_tmul,
    HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit]

private lemma sum_counit_tmul_augmentationDifference {a : A} {ι : Type*}
    (r : Coalgebra.Repr k a ι) :
    ∑ i ∈ r.index,
        algebraMap k A (Coalgebra.counit (R := k) (r.left i)) ⊗ₜ[k]
          augmentationDifference k A (r.right i) =
      1 ⊗ₜ[k] augmentationDifference k A a := by
  simp_rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
    ← map_smul]
  rw [← TensorProduct.tmul_sum, ← map_sum, Coalgebra.sum_counit_smul]

private lemma differentialToCotangent_invariantCotangent_toCotangent
    (x : augIdeal k A) :
    differentialToCotangent k A
        (invariantCotangent k A ((augIdeal k A).toCotangent x)) =
      1 ⊗ₜ[k] (augIdeal k A).toCotangent x := by
  let r := ℛ k (x : A)
  let rr := fun i ↦ ℛ k (r.right i)
  let rl := fun i ↦ ℛ k (r.left i)
  rw [invariantCotangent, Ideal.Cotangent.lift_toCotangent]
  change differentialToCotangent k A (invariantDifferentialRaw k A (x : A)) = _
  rw [invariantDifferentialRaw_apply_repr k A r]
  simp only [map_sum, map_smul, differentialToCotangent,
    Derivation.liftKaehlerDifferential_comp_D]
  simp_rw [cotangentDerivation_apply_repr k A (rr _)]
  simp only [Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul]
  rw [coassoc_tripleCotangent]
  calc
    _ = ∑ i ∈ r.index,
          algebraMap k A (Coalgebra.counit (R := k) (r.left i)) ⊗ₜ[k]
            augmentationDifference k A (r.right i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sum_antipode_mul_tmul k A (rl i) (augmentationDifference k A (r.right i))
    _ = 1 ⊗ₜ[k] augmentationDifference k A (x : A) :=
      sum_counit_tmul_augmentationDifference k A r
    _ = _ := by rw [augmentationDifference_mem]

private lemma differentialToCotangent_comp_cotangentToDifferential :
    (differentialToCotangent k A).comp (cotangentToDifferential k A) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    change differentialToCotangent k A (cotangentToDifferential k A x) = x at hx
    change differentialToCotangent k A (cotangentToDifferential k A y) = y at hy
    simp only [map_add]
    change differentialToCotangent k A (cotangentToDifferential k A x) +
      differentialToCotangent k A (cotangentToDifferential k A y) = x + y
    rw [hx, hy]
  | tmul a m =>
    obtain ⟨x, rfl⟩ := (augIdeal k A).toCotangent_surjective m
    change differentialToCotangent k A
        (cotangentToDifferential k A (a ⊗ₜ[k] (augIdeal k A).toCotangent x)) =
      a ⊗ₜ[k] (augIdeal k A).toCotangent x
    rw [cotangentToDifferential, LinearMap.liftBaseChange_tmul, map_smul,
      differentialToCotangent_invariantCotangent_toCotangent]
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private noncomputable def kaehlerDifferentialEquiv :
  Ω[A⁄k] ≃ₗ[A] A ⊗[k] augCotangent k A :=
  LinearEquiv.ofLinearMap (differentialToCotangent k A) (cotangentToDifferential k A)
    (differentialToCotangent_comp_cotangentToDifferential k A)
    (cotangentToDifferential_comp_differentialToCotangent k A)

public theorem commutativeHopfAlgebra_kaehlerDifferential_free : Module.Free A Ω[A⁄k] := by
  exact Module.Free.of_equiv (kaehlerDifferentialEquiv k A).symm

end Theory.AlgebraicGroup
