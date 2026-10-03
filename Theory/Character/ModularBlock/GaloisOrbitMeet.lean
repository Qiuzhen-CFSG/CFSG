module

public import Theory.Character.ModularBlock.GaloisDescent

/-!
# Products of Galois conjugates of central idempotents

Multiplying every Galois conjugate inside the commutative center produces
an invariant idempotent below the original one. A fixed ambient factor
continues to contain this product. Augmentation one is preserved by every
Galois automorphism and by products, so this invariant factor is nonzero.
For the complement of a factor, the original factor annihilates the product.
These facts enable descent in the finite-field primitivity argument.

Ported from the OrbitMeet section of
`c3503435:glauberman_zStar/Submission/ZStar/FiniteFieldPrimitivity.lean`.
The center action and orbit product are exposed for downstream calculations.
-/

public section
noncomputable section
namespace ModularBlock.FiniteFieldPrimitivity
attribute [local instance] Fintype.ofFinite
open scoped BigOperators

section OrbitMeet

variable (k K : Type*) [Field k] [Field K]
variable [Algebra k K]
variable (H : Type*) [Group H]

@[expose] noncomputable def conjugateCenterHom (σ : K ≃ₐ[k] K) :
    Subring.center (MonoidAlgebra K H) →+*
      Subring.center (MonoidAlgebra K H) where
  toFun z := ⟨conjugate k K H σ z.1,
    conjugate_mem_center k K H σ z.1 z.2⟩
  map_zero' := Subtype.ext (conjugate_zero k K H σ)
  map_one' := Subtype.ext (conjugate_one k K H σ)
  map_add' x y := Subtype.ext (conjugate_add k K H σ x.1 y.1)
  map_mul' x y := Subtype.ext (conjugate_mul k K H σ x.1 y.1)

@[simp] theorem conjugateCenterHom_apply_coe
    (σ : K ≃ₐ[k] K) (z : Subring.center (MonoidAlgebra K H)) :
    (conjugateCenterHom k K H σ z : MonoidAlgebra K H) =
      conjugate k K H σ z.1 := rfl

@[simp] theorem conjugate_one_algEquiv (z : MonoidAlgebra K H) :
    conjugate k K H (1 : K ≃ₐ[k] K) z = z := by
  ext h
  simp [conjugate]

@[simp] theorem conjugateCenterHom_one
    (z : Subring.center (MonoidAlgebra K H)) :
    conjugateCenterHom k K H (1 : K ≃ₐ[k] K) z = z := by
  apply Subtype.ext
  exact conjugate_one_algEquiv k K H z.1

variable [Finite K]

/-- Product of every Galois conjugate of a central element. -/
@[expose] noncomputable def orbitMeet
    (z : Subring.center (MonoidAlgebra K H)) :
    Subring.center (MonoidAlgebra K H) :=
  ∏ σ : K ≃ₐ[k] K, conjugateCenterHom k K H σ z

theorem conjugateCenterHom_orbitMeet
    (τ : K ≃ₐ[k] K) (z : Subring.center (MonoidAlgebra K H)) :
    conjugateCenterHom k K H τ (orbitMeet k K H z) =
      orbitMeet k K H z := by
  rw [orbitMeet, map_prod]
  calc
    (∏ σ : K ≃ₐ[k] K,
        conjugateCenterHom k K H τ (conjugateCenterHom k K H σ z)) =
        ∏ σ : K ≃ₐ[k] K, conjugateCenterHom k K H (τ * σ) z := by
      apply Finset.prod_congr rfl
      intro σ _hσ
      apply Subtype.ext
      exact conjugate_conjugate k K H τ σ z.1
    _ = ∏ σ : K ≃ₐ[k] K, conjugateCenterHom k K H σ z :=
      (Group.mulLeft_bijective τ).prod_comp
        (fun σ : K ≃ₐ[k] K => conjugateCenterHom k K H σ z)

theorem orbitMeet_fixed
    (τ : K ≃ₐ[k] K) (z : Subring.center (MonoidAlgebra K H)) :
    conjugate k K H τ (orbitMeet k K H z).1 =
      (orbitMeet k K H z).1 := by
  exact congrArg Subtype.val (conjugateCenterHom_orbitMeet k K H τ z)

theorem orbitMeet_isIdempotent
    (z : Subring.center (MonoidAlgebra K H))
    (hz : IsIdempotentElem z.1) :
    IsIdempotentElem (orbitMeet k K H z).1 := by
  have hprod : IsIdempotentElem (orbitMeet k K H z) := by
    rw [orbitMeet, IsIdempotentElem, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro σ _hσ
    apply Subtype.ext
    exact conjugate_isIdempotent k K H σ z.1 hz
  exact congrArg Subtype.val hprod

theorem orbitMeet_mul_original
    (z : Subring.center (MonoidAlgebra K H))
    (hz : IsIdempotentElem z.1) :
    (orbitMeet k K H z).1 * z.1 = (orbitMeet k K H z).1 := by
  classical
  have hzCenter : IsIdempotentElem z := by
    exact Subtype.ext hz
  have hresult : orbitMeet k K H z * z = orbitMeet k K H z := by
    rw [orbitMeet,
      Fintype.prod_eq_mul_prod_compl (1 : K ≃ₐ[k] K),
      conjugateCenterHom_one]
    rw [mul_assoc,
      mul_comm (∏ i ∈ ({1} : Finset (K ≃ₐ[k] K))ᶜ,
        conjugateCenterHom k K H i z) z,
      ← mul_assoc, hzCenter.eq]
  exact congrArg Subtype.val hresult

theorem original_mul_orbitMeet_sub_eq_zero
    (e z : Subring.center (MonoidAlgebra K H))
    (hz : IsIdempotentElem z.1)
    (hfactor : z.1 * e.1 = z.1) :
    z.1 * (orbitMeet k K H (e - z)).1 = 0 := by
  classical
  have hzCenter : IsIdempotentElem z := Subtype.ext hz
  have hfactorCenter : z * e = z := Subtype.ext hfactor
  have hzsub : z * (e - z) = 0 := by
    rw [mul_sub, hfactorCenter, hzCenter.eq, sub_self]
  have hresult : z * orbitMeet k K H (e - z) = 0 := by
    rw [orbitMeet,
      Fintype.prod_eq_mul_prod_compl (1 : K ≃ₐ[k] K),
      conjugateCenterHom_one, ← mul_assoc, hzsub, zero_mul]
  exact congrArg Subtype.val hresult

theorem orbitMeet_factor
    (e z : Subring.center (MonoidAlgebra K H))
    (he : IsIdempotentElem e.1)
    (hefixed : ∀ σ : K ≃ₐ[k] K, conjugate k K H σ e.1 = e.1)
    (hfactor : z.1 * e.1 = z.1) :
    (orbitMeet k K H z).1 * e.1 = (orbitMeet k K H z).1 := by
  have hcard : Fintype.card (K ≃ₐ[k] K) ≠ 0 :=
    Nat.ne_of_gt Fintype.card_pos
  have heprod :
      (∏ _σ : K ≃ₐ[k] K, e) = e := by
    rw [Finset.prod_const]
    apply Subtype.ext
    exact he.pow_eq hcard
  have hfactorCenter : z * e = z := Subtype.ext hfactor
  have hresult : orbitMeet k K H z * e = orbitMeet k K H z := by
    calc
      orbitMeet k K H z * e =
          orbitMeet k K H z * (∏ _σ : K ≃ₐ[k] K, e) := by rw [heprod]
      _ = ∏ σ : K ≃ₐ[k] K,
          (conjugateCenterHom k K H σ z * e) :=
        (Finset.prod_mul_distrib).symm
      _ = ∏ σ : K ≃ₐ[k] K, conjugateCenterHom k K H σ z := by
        apply Finset.prod_congr rfl
        intro σ _hσ
        apply Subtype.ext
        exact conjugate_factor k K H σ e.1 z.1 (hefixed σ) hfactor
      _ = orbitMeet k K H z := rfl
  exact congrArg Subtype.val hresult

omit [Finite K] in
theorem augmentation_conjugate
    (σ : K ≃ₐ[k] K) (z : MonoidAlgebra K H) :
    groupAlgebraAugmentation K H (conjugate k K H σ z) =
      σ (groupAlgebraAugmentation K H z) := by
  exact groupAlgebraAugmentation_mapRingHom σ.toRingEquiv.toRingHom z

theorem orbitMeet_augmentation_eq_one
    (z : Subring.center (MonoidAlgebra K H))
    (hzaug : groupAlgebraAugmentation K H z.1 = 1) :
    groupAlgebraAugmentation K H (orbitMeet k K H z).1 = 1 := by
  let augZ : Subring.center (MonoidAlgebra K H) →+* K :=
    (groupAlgebraAugmentation K H).toRingHom.comp
      (Subring.center (MonoidAlgebra K H)).subtype
  change augZ (orbitMeet k K H z) = 1
  rw [orbitMeet, map_prod]
  have hterm : ∀ σ : K ≃ₐ[k] K,
      augZ (conjugateCenterHom k K H σ z) = 1 := by
    intro σ
    change groupAlgebraAugmentation K H
      (conjugate k K H σ z.1) = 1
    rw [augmentation_conjugate, hzaug, map_one]
  simp [hterm]

theorem orbitMeet_ne_zero_of_augmentation_eq_one
    (z : Subring.center (MonoidAlgebra K H))
    (hzaug : groupAlgebraAugmentation K H z.1 = 1) :
    (orbitMeet k K H z).1 ≠ 0 := by
  intro hzero
  have haug := orbitMeet_augmentation_eq_one k K H z hzaug
  rw [hzero, map_zero] at haug
  exact zero_ne_one haug

end OrbitMeet


end ModularBlock.FiniteFieldPrimitivity

