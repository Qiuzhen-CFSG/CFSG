module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers.ConcreteModels.Scalars
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Normalizer
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# The normalizer of the six-point augmentation action

A normalizing operator preserves the fixed line, which is exactly the kernel
of the map to the natural module. It therefore descends to the literal natural
A₆ image. Its normalizer is the known S₆ image. Faithfulness of that natural
action identifies the original conjugation on A₆, and the scalar commutant of
the augmentation core then makes the original operator the same permutation.
No complement to the fixed line is used.

Source: Aschbacher–Smith, B.5.7, printed p.106, the five-dimensional core branch;
natural-module conventions from B.3.1, printed p.83.
-/

open BinaryPermutation Representation
open LinearMap.GeneralLinearGroup
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers.ConcreteModels
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
private abbrev C := core (Fin 6)
private abbrev N := natural (Fin 6)
private abbrev A := alternatingGroup (Fin 6)
private abbrev R := coreRepresentation (Fin 6)
private abbrev Q := coreToNatural (Fin 6)
private abbrev H := (alternatingCoreRepresentation (Fin 6)).asGroupHom
private abbrev CoreGL := (Module.End (ZMod 2) C)ˣ

private theorem ker_fixed (v : C) : v ∈ Q.ker ↔ ∀ a : A, R a v = v := by
  have hk : v ∈ Q.ker ↔ v.val ∈ constants (Fin 6) := by
    change Q v = 0 ↔ _
    rw [← Subtype.val_inj]
    exact Submodule.Quotient.mk_eq_zero _
  rw [hk]
  constructor
  · intro hv a
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    apply Subtype.ext
    change representation _ a v.val = v.val
    rw [← hc, map_smul, permute_allOne]
  · intro hv
    apply Submodule.mem_span_singleton.mpr
    refine ⟨v.val 0, ?_⟩
    ext i
    have := alternatingGroup.isPretransitive_of_three_le_card (Fin 6) (by simp)
    obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A (0 : Fin 6) i
    have hai : a.val.symm i = 0 := by
      rw [← show a.val 0 = i from ha, a.val.symm_apply_apply]
    have hh := congrArg (fun w : C => w.val i) (hv a)
    change v.val (a.val.symm i) = v.val i at hh
    simpa only [hai, Pi.smul_apply, allOne, smul_eq_mul, mul_one] using hh

private theorem conjugate_action (u : CoreGL)
    (hu : u ∈ Subgroup.normalizer (H.range : Set CoreGL)) (a : A) :
    ∃ b : A, ∀ v, u.val (R a v) = R b (u.val v) := by
  obtain ⟨b, hb⟩ := (Subgroup.mem_normalizer_iff.mp hu (H a)).mp ⟨a, rfl⟩
  refine ⟨b, fun v => ?_⟩
  have he : u * H a = H b * u := by
    rw [hb, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
  exact LinearMap.congr_fun (congrArg Units.val he) v

private theorem normalizer_ker (u : CoreGL)
    (hu : u ∈ Subgroup.normalizer (H.range : Set CoreGL)) :
    Q.ker.map u.val = Q.ker := by
  have stable (u : CoreGL) (hu : u ∈ Subgroup.normalizer (H.range : Set CoreGL))
      (v : C) (hv : v ∈ Q.ker) : u.val v ∈ Q.ker := by
    apply (ker_fixed _).mpr
    intro a
    obtain ⟨b, hb⟩ := conjugate_action u⁻¹ (Subgroup.inv_mem _ hu) a
    apply (toLinearEquiv u⁻¹).injective
    change u.inv (R a (u.val v)) = u.inv (u.val v)
    have he := hb (u.val v)
    change u.inv (R a (u.val v)) = R b (u.inv (u.val v)) at he
    rw [show u.inv (u.val v) = v from (toLinearEquiv u).symm_apply_apply v] at he ⊢
    exact he.trans ((ker_fixed v).mp hv b)
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact stable u hu v hv
  · intro v hv
    refine ⟨u.inv v, stable u⁻¹ (Subgroup.inv_mem _ hu) v hv, ?_⟩
    exact (toLinearEquiv u).apply_symm_apply v

private noncomputable def quotientEquiv (u : CoreGL)
    (hu : u ∈ Subgroup.normalizer (H.range : Set CoreGL)) : N ≃ₗ[ZMod 2] N :=
  let e := Q.quotKerEquivOfSurjective coreToNatural_surjective
  e.symm.trans ((Submodule.Quotient.equiv Q.ker Q.ker (toLinearEquiv u)
    (normalizer_ker u hu)).trans e)

private theorem quotientEquiv_apply (u : CoreGL)
    (hu : u ∈ Subgroup.normalizer (H.range : Set CoreGL)) (v : C) :
    quotientEquiv u hu (Q v) = Q (u.val v) := by
  simp only [quotientEquiv, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

private theorem quotient_conjugate (u : CoreGL)
    (hu : u ∈ Subgroup.normalizer (H.range : Set CoreGL)) (a b : A)
    (hab : ∀ v, u.val (R a v) = R b (u.val v)) :
    ∀ v, quotientEquiv u hu (alternatingAction a v) =
      alternatingAction b (quotientEquiv u hu v) := by
  intro v
  obtain ⟨w, rfl⟩ := coreToNatural_surjective v
  change quotientEquiv u hu (naturalRepresentation _ a (Q w)) =
    naturalRepresentation _ b (quotientEquiv u hu (Q w))
  rw [← coreToNatural_equivariant, quotientEquiv_apply, quotientEquiv_apply,
    hab, coreToNatural_equivariant]

private theorem quotient_normalizes (u : CoreGL)
    (hu : u ∈ Subgroup.normalizer (H.range : Set CoreGL)) :
    ofLinearEquiv (quotientEquiv u hu) ∈
      Subgroup.normalizer (alternatingImage : Set LinearGroup) := by
  let f := quotientEquiv u hu
  let U := ofLinearEquiv f
  have hconj (a : A) : U * alternatingHom a * U⁻¹ ∈ alternatingImage := by
    obtain ⟨b, hb⟩ := conjugate_action u hu a
    refine ⟨b, ?_⟩
    apply Units.ext
    apply LinearMap.ext
    intro v
    have hh := quotient_conjugate u hu a b hb (f.symm v)
    change f (alternatingAction a (f.symm v)) =
      alternatingAction b (f (f.symm v)) at hh
    change alternatingAction b v = f (alternatingAction a (f.symm v))
    simpa only [f.apply_symm_apply] using hh.symm
  have hinv (a : A) : U⁻¹ * alternatingHom a * U ∈ alternatingImage := by
    obtain ⟨b, hb⟩ := conjugate_action u⁻¹ (Subgroup.inv_mem _ hu) a
    have hab (v : C) : u.val (R b v) = R a (u.val v) := by
      have hh := congrArg u.val (hb (u.val v))
      change u.val (u.inv (R a (u.val v))) = u.val (R b (u.inv (u.val v))) at hh
      have hi (w : C) : u.val (u.inv w) = w := (toLinearEquiv u).apply_symm_apply w
      have hi' (w : C) : u.inv (u.val w) = w := (toLinearEquiv u).symm_apply_apply w
      rw [hi, hi'] at hh
      exact hh.symm
    refine ⟨b, ?_⟩
    apply Units.ext
    apply LinearMap.ext
    intro v
    have hh := quotient_conjugate u hu b a hab v
    change f (alternatingAction b v) = alternatingAction a (f v) at hh
    exact f.eq_symm_apply.mpr hh
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · rintro ⟨a, rfl⟩
    exact hconj a
  · rintro ⟨a, ha⟩
    have hh := hinv a
    change alternatingHom a = U * x * U⁻¹ at ha
    rw [ha] at hh
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh

/-- The full linear normalizer of the literal A₆ augmentation image is the literal S₆ image. -/
public theorem core_six_normalizer :
    Subgroup.normalizer ((Representation.asGroupHom ((coreRepresentation (Fin 6)).comp
      (alternatingGroup (Fin 6)).subtype)).range :
      Set (Module.End (ZMod 2) (core (Fin 6)))ˣ) =
    (coreRepresentation (Fin 6)).asGroupHom.range := by
  apply le_antisymm
  · intro u hu
    have hq := quotient_normalizes u hu
    rw [normalizer_alternatingImage] at hq
    obtain ⟨s, hs⟩ := hq
    have hsQ (v : C) : Q (u.val v) = naturalRepresentation _ s (Q v) := by
      rw [← quotientEquiv_apply u hu]
      exact (LinearMap.congr_fun (congrArg Units.val hs) (Q v)).symm
    have hconj (a : A) (v : C) :
        u.val (R a v) = R (s * a.val * s⁻¹) (u.val v) := by
      obtain ⟨b, hb⟩ := conjugate_action u hu a
      have hquot (w : N) :
          naturalRepresentation _ b (naturalRepresentation _ s w) =
            naturalRepresentation _ s (naturalRepresentation _ a w) := by
        obtain ⟨z, rfl⟩ := coreToNatural_surjective w
        rw [← hsQ, ← coreToNatural_equivariant, ← hb, hsQ, coreToNatural_equivariant]
      have he : (b : Equiv.Perm (Fin 6)) * s = s * a.val := by
        apply symmetricAction_injective
        apply LinearMap.ext
        intro w
        change naturalRepresentation _ (b.val * s) w = naturalRepresentation _ (s * a.val) w
        rw [map_mul, map_mul]
        exact hquot w
      have hbval : b.val = s * a.val * s⁻¹ := by
        rw [← he, mul_assoc, mul_inv_cancel, mul_one]
      rw [hb, hbval]
    let f : C ≃ₗ[ZMod 2] C := (toLinearEquiv u).trans
      (LinearEquiv.ofBijective (R s⁻¹) (R.apply_bijective _))
    have hf : f = LinearEquiv.refl (ZMod 2) C := by
      apply equiv_eq_refl_of_scalar
      apply core_six_scalar f.toLinearMap
      intro a v
      change R s⁻¹ (u.val (R a v)) = R a (R s⁻¹ (u.val v))
      rw [hconj]
      change (R s⁻¹ * R (s * a.val * s⁻¹)) (u.val v) =
        (R a.val * R s⁻¹) (u.val v)
      rw [← map_mul, ← map_mul]
      congr 2
      group
    refine ⟨s, ?_⟩
    apply Units.ext
    apply LinearMap.ext
    intro v
    have he := congrArg (fun f : C ≃ₗ[ZMod 2] C => R s (f v)) hf
    change R s (R s⁻¹ (u.val v)) = R s v at he
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] at he
    exact he.symm
  · have he : H.range = (alternatingGroup (Fin 6)).map R.asGroupHom := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a.val, a.property, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
    have hh := (alternatingGroup (Fin 6)).le_normalizer_map R.asGroupHom
    rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, ← he] at hh
    exact hh
end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers.ConcreteModels
