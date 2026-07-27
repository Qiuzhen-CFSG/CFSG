import Submission.ZStar.CompatibleBrauerBlock
import Submission.ZStar.CyclotomicDVR
import Mathlib.FieldTheory.Finite.Extension

/-!
# Central primitivity under finite residue-field extension

This file isolates the field-theoretic part of the compatible local selector
argument.  A central idempotent over a finite field which is primitive and has
augmentation one remains primitive after extension to a finite field.  The
proof uses Galois orbit products/joins and coefficientwise descent.
-/

noncomputable section

namespace Submission.ZStar
namespace FiniteFieldPrimitivity

universe u v

attribute [local instance] Fintype.ofFinite

open scoped BigOperators

/-- Central primitivity, stated in a namespace independent of the block files. -/
def IsCentrallyPrimitive {A : Type*} [Ring A] (e : A) : Prop :=
  e ∈ Set.center A ∧ IsIdempotentElem e ∧ e ≠ 0 ∧
    ∀ f : A, f ∈ Set.center A → IsIdempotentElem f →
      f * e = f → f ≠ 0 → f = e

/-- Mapping coefficients preserves the center of a group algebra. -/
theorem mapRingHom_mem_center
    {R S : Type*} [CommRing R] [CommRing S]
    {H : Type*} [Group H]
    (φ : R →+* S) (e : MonoidAlgebra R H)
    (he : e ∈ Set.center (MonoidAlgebra R H)) :
    MonoidAlgebra.mapRingHom H φ e ∈
      Set.center (MonoidAlgebra S H) := by
  apply (Semigroup.mem_center_iff).2
  intro a
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, mul_add, hx, hy]
  | single g r =>
      have hcomm := Semigroup.mem_center_iff.mp he
        (MonoidAlgebra.single g (1 : R))
      have hmap := congrArg (MonoidAlgebra.mapRingHom H φ) hcomm
      have hcommOne :
          (MonoidAlgebra.single g (1 : S)) *
              MonoidAlgebra.mapRingHom H φ e =
            MonoidAlgebra.mapRingHom H φ e *
              MonoidAlgebra.single g (1 : S) := by
        simpa using hmap
      rw [show (MonoidAlgebra.single g r : MonoidAlgebra S H) =
          r • MonoidAlgebra.single g 1 by simp]
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
      exact congrArg (fun x : MonoidAlgebra S H => r • x) hcommOne

section GaloisHelpers

variable (k K : Type*) [Field k] [Finite k] [Field K] [Finite K]
variable [Algebra k K]
variable (H : Type*) [Group H]

noncomputable def conjugate
    (σ : K ≃ₐ[k] K) (x : MonoidAlgebra K H) : MonoidAlgebra K H :=
  MonoidAlgebra.mapRingEquiv H σ.toRingEquiv x

@[simp] theorem conjugate_apply (σ : K ≃ₐ[k] K)
    (x : MonoidAlgebra K H) (h : H) :
    conjugate k K H σ x h = σ (x h) := by
  simp [conjugate]

@[simp] theorem conjugate_zero (σ : K ≃ₐ[k] K) :
    conjugate k K H σ (0 : MonoidAlgebra K H) = 0 := by
  simp [conjugate]

@[simp] theorem conjugate_one (σ : K ≃ₐ[k] K) :
    conjugate k K H σ (1 : MonoidAlgebra K H) = 1 := by
  simp [conjugate]

@[simp] theorem conjugate_add (σ : K ≃ₐ[k] K)
    (x y : MonoidAlgebra K H) :
    conjugate k K H σ (x + y) = conjugate k K H σ x + conjugate k K H σ y := by
  simp [conjugate]

@[simp] theorem conjugate_sub (σ : K ≃ₐ[k] K)
    (x y : MonoidAlgebra K H) :
    conjugate k K H σ (x - y) = conjugate k K H σ x - conjugate k K H σ y := by
  simp [conjugate]

@[simp] theorem conjugate_mul (σ : K ≃ₐ[k] K)
    (x y : MonoidAlgebra K H) :
    conjugate k K H σ (x * y) = conjugate k K H σ x * conjugate k K H σ y := by
  simp [conjugate]

@[simp] theorem conjugate_conjugate (τ σ : K ≃ₐ[k] K)
    (x : MonoidAlgebra K H) :
    conjugate k K H τ (conjugate k K H σ x) =
      conjugate k K H (τ * σ) x := by
  ext h
  simp [conjugate, AlgEquiv.mul_apply]

theorem conjugate_algebraMap
    (σ : K ≃ₐ[k] K) (x : MonoidAlgebra k H) :
    conjugate k K H σ
        (MonoidAlgebra.mapRingHom H (algebraMap k K) x) =
      MonoidAlgebra.mapRingHom H (algebraMap k K) x := by
  ext h
  simp [conjugate]

theorem conjugate_mapRingHom
    (σ : K ≃ₐ[k] K) (x : MonoidAlgebra K H) :
    conjugate k K H σ x =
      MonoidAlgebra.mapRingHom H σ.toRingEquiv.toRingHom x := rfl

theorem conjugate_mem_center
    (σ : K ≃ₐ[k] K) (x : MonoidAlgebra K H)
    (hx : x ∈ Set.center (MonoidAlgebra K H)) :
    conjugate k K H σ x ∈ Set.center (MonoidAlgebra K H) := by
  apply (Semigroup.mem_center_iff).2
  intro a
  let E := MonoidAlgebra.mapRingEquiv H σ.toRingEquiv
  have h := Semigroup.mem_center_iff.mp hx
    (E.symm a)
  calc
    a * conjugate k K H σ x = E (E.symm a) * E x := by
      rw [E.apply_symm_apply]
      rfl
    _ = E (E.symm a * x) := (E.map_mul _ _).symm
    _ = E (x * E.symm a) := congrArg E h
    _ = E x * E (E.symm a) := E.map_mul _ _
    _ = conjugate k K H σ x * a := by rw [E.apply_symm_apply]; rfl

theorem conjugate_isIdempotent
    (σ : K ≃ₐ[k] K) (x : MonoidAlgebra K H)
    (hx : IsIdempotentElem x) :
    IsIdempotentElem (conjugate k K H σ x) := by
  let E := MonoidAlgebra.mapRingEquiv H σ.toRingEquiv
  change E x * E x = E x
  rw [← E.map_mul, hx]

theorem conjugate_factor
    (σ : K ≃ₐ[k] K) (e f : MonoidAlgebra K H)
    (hefixed : conjugate k K H σ e = e)
    (hfactor : f * e = f) :
    conjugate k K H σ f * e = conjugate k K H σ f := by
  rw [← hefixed, ← conjugate_mul]
  exact congrArg (conjugate k K H σ) hfactor

theorem exists_preimage_of_galois_fixed
    (y : MonoidAlgebra K H)
    (hy : ∀ σ : K ≃ₐ[k] K, conjugate k K H σ y = y) :
    ∃ x : MonoidAlgebra k H,
      MonoidAlgebra.mapRingHom H (algebraMap k K) x = y := by
  classical
  have hcoeff : ∀ h : H, y h ∈ Set.range (algebraMap k K) := by
    intro h
    apply (IsGalois.mem_range_algebraMap_iff_fixed
      (F := k) (E := K) (y h)).2
    intro σ
    have hs := congrArg (fun a : MonoidAlgebra K H => a h) (hy σ)
    simpa [conjugate_apply] using hs
  have hyRange :
      y ∈ Set.range
        (MonoidAlgebra.map (M := H) (algebraMap k K).toAddMonoidHom) := by
    rw [MonoidAlgebra.range_map]
    exact hcoeff
  rcases hyRange with ⟨x, hx⟩
  exact ⟨x, hx⟩

end GaloisHelpers

section OrbitMeet

variable (k K : Type*) [Field k] [Finite k] [Field K] [Finite K]
variable [Algebra k K]
variable (H : Type*) [Group H]

noncomputable def conjugateCenterHom (σ : K ≃ₐ[k] K) :
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

/-- Product of every Galois conjugate of a central element. -/
noncomputable def orbitMeet
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

theorem augmentation_conjugate
    (σ : K ≃ₐ[k] K) (z : MonoidAlgebra K H) :
    AugmentationScratch.augmentation K H (conjugate k K H σ z) =
      σ (AugmentationScratch.augmentation K H z) := by
  exact AugmentationScratch.augmentation_mapRingHom σ.toRingEquiv.toRingHom z

theorem orbitMeet_augmentation_eq_one
    (z : Subring.center (MonoidAlgebra K H))
    (hzaug : AugmentationScratch.augmentation K H z.1 = 1) :
    AugmentationScratch.augmentation K H (orbitMeet k K H z).1 = 1 := by
  let augZ : Subring.center (MonoidAlgebra K H) →+* K :=
    (AugmentationScratch.augmentation K H).comp
      (Subring.center (MonoidAlgebra K H)).subtype
  change augZ (orbitMeet k K H z) = 1
  rw [orbitMeet, map_prod]
  have hterm : ∀ σ : K ≃ₐ[k] K,
      augZ (conjugateCenterHom k K H σ z) = 1 := by
    intro σ
    change AugmentationScratch.augmentation K H
      (conjugate k K H σ z.1) = 1
    rw [augmentation_conjugate, hzaug, map_one]
  simp [hterm]

theorem orbitMeet_ne_zero_of_augmentation_eq_one
    (z : Subring.center (MonoidAlgebra K H))
    (hzaug : AugmentationScratch.augmentation K H z.1 = 1) :
    (orbitMeet k K H z).1 ≠ 0 := by
  intro hzero
  have haug := orbitMeet_augmentation_eq_one k K H z hzaug
  rw [hzero, map_zero] at haug
  exact zero_ne_one haug

end OrbitMeet

section Descent

variable (k K : Type*) [Field k] [Finite k] [Field K] [Finite K]
variable [Algebra k K]
variable (H : Type*) [Group H]

private theorem mapGroupAlgebra_injective :
    Function.Injective
      (MonoidAlgebra.mapRingHom H (algebraMap k K)) := by
  exact MonoidAlgebra.map_injective (algebraMap k K).toAddMonoidHom
    (algebraMap k K).injective

theorem fixed_central_idempotent_factor_eq_map_of_source_primitive
    (e : MonoidAlgebra k H)
    (hprimitive : IsCentrallyPrimitive e)
    (y : MonoidAlgebra K H)
    (hyfixed : ∀ σ : K ≃ₐ[k] K, conjugate k K H σ y = y)
    (hycenter : y ∈ Set.center (MonoidAlgebra K H))
    (hyidem : IsIdempotentElem y)
    (hyfactor :
      y * MonoidAlgebra.mapRingHom H (algebraMap k K) e = y)
    (hyne : y ≠ 0) :
    y = MonoidAlgebra.mapRingHom H (algebraMap k K) e := by
  obtain ⟨x, hxmap⟩ :=
    exists_preimage_of_galois_fixed k K H y hyfixed
  have hmapinj := mapGroupAlgebra_injective k K H
  have hxcenter : x ∈ Set.center (MonoidAlgebra k H) := by
    apply (Semigroup.mem_center_iff).2
    intro a
    apply hmapinj
    rw [map_mul, map_mul, hxmap]
    exact Semigroup.mem_center_iff.mp hycenter
      (MonoidAlgebra.mapRingHom H (algebraMap k K) a)
  have hxidem : IsIdempotentElem x := by
    apply hmapinj
    rw [map_mul, hxmap, hyidem]
  have hxfactor : x * e = x := by
    apply hmapinj
    rw [map_mul, hxmap, hyfactor]
  have hxne : x ≠ 0 := by
    intro hxzero
    apply hyne
    rw [← hxmap, hxzero, map_zero]
  have hxeq : x = e :=
    hprimitive.2.2.2 x hxcenter hxidem hxfactor hxne
  rw [← hxmap, hxeq]

end Descent

section MainTheorem

variable (k K : Type*) [Field k] [Finite k] [Field K] [Finite K]
variable [Algebra k K]
variable (H : Type*) [Group H]

/-- An augmentation-one centrally primitive idempotent in a finite-field
group algebra stays centrally primitive after extending to any finite field. -/
theorem map_isCentrallyPrimitive_of_augmentation_eq_one
    (e : MonoidAlgebra k H)
    (hprimitive : IsCentrallyPrimitive e)
    (haugmentation : AugmentationScratch.augmentation k H e = 1) :
    IsCentrallyPrimitive
      (MonoidAlgebra.mapRingHom H (algebraMap k K) e) := by
  classical
  let E := MonoidAlgebra.mapRingHom H (algebraMap k K) e
  have hEcenter : E ∈ Set.center (MonoidAlgebra K H) :=
    mapRingHom_mem_center (algebraMap k K) e hprimitive.1
  have hEidem : IsIdempotentElem E := by
    change MonoidAlgebra.mapRingHom H (algebraMap k K) e *
        MonoidAlgebra.mapRingHom H (algebraMap k K) e =
      MonoidAlgebra.mapRingHom H (algebraMap k K) e
    rw [← map_mul, hprimitive.2.1]
  have hEaugmentation :
      AugmentationScratch.augmentation K H E = 1 := by
    change AugmentationScratch.augmentation K H
      (MonoidAlgebra.mapRingHom H (algebraMap k K) e) = 1
    rw [AugmentationScratch.augmentation_mapRingHom, haugmentation, map_one]
  have hEne : E ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hEaugmentation
    exact zero_ne_one hEaugmentation
  have hEfixed : ∀ σ : K ≃ₐ[k] K, conjugate k K H σ E = E := by
    intro σ
    exact conjugate_algebraMap k K H σ e
  refine ⟨hEcenter, hEidem, hEne, ?_⟩
  intro f hfcenter hfid hfactor hfne
  let Ez : Subring.center (MonoidAlgebra K H) := ⟨E, hEcenter⟩
  let fz : Subring.center (MonoidAlgebra K H) := ⟨f, hfcenter⟩
  have hEf : E * f = f := by
    calc
      E * f = f * E := (Semigroup.mem_center_iff.mp hEcenter f).symm
      _ = f := hfactor
  have haugIdem : IsIdempotentElem
      (AugmentationScratch.augmentation K H f) := by
    change AugmentationScratch.augmentation K H f *
        AugmentationScratch.augmentation K H f =
      AugmentationScratch.augmentation K H f
    rw [← map_mul, hfid]
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp haugIdem with haug0 | haug1
  · let cz : Subring.center (MonoidAlgebra K H) := Ez - fz
    have hcid : IsIdempotentElem cz.1 := by
      change IsIdempotentElem (E - f)
      exact hfid.sub hEidem hfactor hEf
    have hcfactor : cz.1 * E = cz.1 := by
      change (E - f) * E = E - f
      rw [sub_mul, hEidem, hfactor]
    have hcaug : AugmentationScratch.augmentation K H cz.1 = 1 := by
      change AugmentationScratch.augmentation K H (E - f) = 1
      rw [map_sub, hEaugmentation, haug0, sub_zero]
    let nz : Subring.center (MonoidAlgebra K H) := orbitMeet k K H cz
    have hnfixed : ∀ σ : K ≃ₐ[k] K,
        conjugate k K H σ nz.1 = nz.1 := by
      intro σ
      exact orbitMeet_fixed k K H σ cz
    have hnidem : IsIdempotentElem nz.1 :=
      orbitMeet_isIdempotent k K H cz hcid
    have hnfactor : nz.1 * E = nz.1 :=
      orbitMeet_factor k K H Ez cz hEidem hEfixed hcfactor
    have hnne : nz.1 ≠ 0 :=
      orbitMeet_ne_zero_of_augmentation_eq_one k K H cz hcaug
    have hneq : nz.1 = E :=
      fixed_central_idempotent_factor_eq_map_of_source_primitive
        k K H e hprimitive nz.1 hnfixed nz.2 hnidem hnfactor hnne
    have hfzero : f * nz.1 = 0 := by
      exact original_mul_orbitMeet_sub_eq_zero k K H Ez fz hfid hfactor
    rw [hneq] at hfzero
    exact (hfne (hfactor.symm.trans hfzero)).elim
  · let mz : Subring.center (MonoidAlgebra K H) := orbitMeet k K H fz
    have hmfixed : ∀ σ : K ≃ₐ[k] K,
        conjugate k K H σ mz.1 = mz.1 := by
      intro σ
      exact orbitMeet_fixed k K H σ fz
    have hmidem : IsIdempotentElem mz.1 :=
      orbitMeet_isIdempotent k K H fz hfid
    have hmfactor : mz.1 * E = mz.1 :=
      orbitMeet_factor k K H Ez fz hEidem hEfixed hfactor
    have hmne : mz.1 ≠ 0 :=
      orbitMeet_ne_zero_of_augmentation_eq_one k K H fz haug1
    have hmeq : mz.1 = E :=
      fixed_central_idempotent_factor_eq_map_of_source_primitive
        k K H e hprimitive mz.1 hmfixed mz.2 hmidem hmfactor hmne
    have hmulf : mz.1 * f = mz.1 :=
      orbitMeet_mul_original k K H fz hfid
    rw [hmeq] at hmulf
    exact hEf.symm.trans hmulf

end MainTheorem

section CompatibleSelector

open PrincipalBlockConstruction

variable {G : Type u} [Group G] [Finite G]

private theorem principalResidueField_finite
    (d : PrincipalCongruenceBlockData G) :
    Finite (BrauerBlockReduction.principalResidueField d) := by
  have hprime_ne_bot : d.primeIdeal ≠ ⊥ := by
    intro hbot
    have htwo := BlockPreliminaries.two_mem_of_liesOver
      d.primeIdeal d.primeIdeal_liesOverTwo
    have hzero : (2 : Representation.cyclotomicOrder d.eta) = 0 := by
      simpa [hbot] using htwo
    exact two_ne_zero hzero
  exact CyclotomicDVR.cyclotomicOrder_quotient_finite
    (Nat.card_pos (α := G)).ne' d.eta_spec d.primeIdeal hprime_ne_bot

/-- Conditional specialization to the compatible local principal selector.
The only input is central primitivity before extending the residue field. -/
theorem localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive_of_source
    (d : PrincipalCongruenceBlockData G) (H : Subgroup G)
    (hsource : IsCentrallyPrimitive
      (BrauerBlockReduction.reducedPrincipalBlockElement
        (CompatibleBrauerBlock.localData d H))) :
    IsCentrallyPrimitive
      (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d H) := by
  let dH := CompatibleBrauerBlock.localData d H
  let k := BrauerBlockReduction.principalResidueField dH
  let K := BrauerBlockReduction.principalResidueField d
  let φ := CompatibleLocalBlock.compatibleSubgroupResidueFieldInclusion d H
  letI : Field k := Ideal.Quotient.field dH.primeIdeal
  letI : Field K := Ideal.Quotient.field d.primeIdeal
  letI : Finite k := principalResidueField_finite dH
  letI : Finite K := principalResidueField_finite d
  letI : Algebra k K := φ.toAlgebra
  have hgeneric := map_isCentrallyPrimitive_of_augmentation_eq_one
    k K H
    (BrauerBlockReduction.reducedPrincipalBlockElement dH)
    hsource
    (AugmentationScratch.reducedPrincipalBlockElement_augmentation_eq_one dH)
  have halgebraMap : algebraMap k K = φ := rfl
  rw [halgebraMap] at hgeneric
  change IsCentrallyPrimitive
    (MonoidAlgebra.mapRingHom H
      (CompatibleLocalBlock.compatibleSubgroupResidueFieldInclusion d H)
      (BrauerBlockReduction.reducedPrincipalBlockElement dH))
  exact hgeneric

end CompatibleSelector

end FiniteFieldPrimitivity
end Submission.ZStar
