module

public import Theory.Representation.BinaryOffender.Defs
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic

/-!
# Two-subgroups and involutions in a binary Singer normalizer

Let a cyclic subgroup of the general linear group act regularly on the nonzero
vectors of a finite binary vector space. Every two-subgroup of its normalizer
is cyclic, and every nonidentity involution in the normalizer fixes at most
the square root of the number of vectors.

Evaluation at a nonzero vector identifies every nonzero commuting endomorphism
with an element of the cyclic subgroup. Thus the commuting algebra is a field.
Normalizer conjugation acts on this field; its kernel has no nontrivial element
of two-power order, so two-subgroups embed in the cyclic field-automorphism group.
For the fixed-space bound, choose a commuting endomorphism moved by conjugation.
Its difference from its conjugate is invertible, which makes the sum of the fixed
space and its image under that endomorphism direct.

Source: GLS, *The Classification of the Finite Simple Groups*, Number 2,
Chapter C, equation (14.4) and Proposition 14.2, Step 3, citing Huppert II.3.11;
`refs/KGroup/GLS2/ChapterC.tex`. The conjugation construction adapts the private
commuting-algebra argument of `Theory.Representation.SingerFour`, here using
regularity to construct the field directly. Conjugation here is on the left.
-/

noncomputable section

namespace Representation.BinarySingerNormalizer

open scoped IsMulCommutative

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

private abbrev action : LinearMap.GeneralLinearGroup (ZMod 2) W →* Module.End (ZMod 2) W :=
  Units.coeHom (Module.End (ZMod 2) W)
private abbrev algebra (C : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)) :=
  Subalgebra.centralizer (ZMod 2) (Set.range (action.comp C.subtype))

variable (C : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W))
variable (hreg : ∀ v w : W, v ≠ 0 → w ≠ 0 → ∃! c : C, (c.val : Module.End (ZMod 2) W) v = w)

include hreg in
private theorem eval_injective (v : W) (hv : v ≠ 0) :
    Function.Injective (fun f : algebra C => f.val v) := by
  intro f g h
  apply Subtype.ext
  ext w
  by_cases hw : w = 0
  · simp [hw]
  obtain ⟨c, hc, _⟩ := hreg v w hv hw
  have hf := congrArg (fun a : Module.End (ZMod 2) W => a v) (f.property _ ⟨c, rfl⟩)
  have hg := congrArg (fun a : Module.End (ZMod 2) W => a v) (g.property _ ⟨c, rfl⟩)
  change (c.val : Module.End (ZMod 2) W) (f.val v) = f.val ((c.val : Module.End (ZMod 2) W) v) at hf
  change (c.val : Module.End (ZMod 2) W) (g.val v) = g.val ((c.val : Module.End (ZMod 2) W) v) at hg
  rw [hc] at hf hg
  exact hf.symm.trans ((congrArg (c.val : Module.End (ZMod 2) W) h).trans hg)

variable [IsCyclic C]

private def scalar : C →* algebra C where
  toFun c := ⟨(c.val : Module.End (ZMod 2) W), by
    rintro _ ⟨d, rfl⟩
    exact congrArg (fun x : C => (x.val : Module.End (ZMod 2) W)) (mul_comm d c)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

include hreg in
private theorem exists_scalar [Nontrivial W] (f : algebra C) (hf : f ≠ 0) :
    ∃ c : C, scalar C c = f := by
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  have hfv : f.val v ≠ 0 := by
    intro h
    apply hf
    exact eval_injective C hreg v hv h
  obtain ⟨c, hc, _⟩ := hreg v (f.val v) hv hfv
  exact ⟨c, eval_injective C hreg v hv hc⟩

@[instance_reducible]
private def field [Nontrivial W] : Field (algebra C) := by
  apply IsField.toField
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨0, 1, zero_ne_one⟩
  · intro f g
    by_cases hf : f = 0
    · simp [hf]
    by_cases hg : g = 0
    · simp [hg]
    obtain ⟨c, rfl⟩ := exists_scalar C hreg f hf
    obtain ⟨d, rfl⟩ := exists_scalar C hreg g hg
    rw [← map_mul, ← map_mul, mul_comm c d]
  · intro f hf
    obtain ⟨c, rfl⟩ := exists_scalar C hreg f hf
    exact ⟨scalar C c⁻¹, by rw [← map_mul, mul_inv_cancel, map_one]⟩

private theorem scalar_injective (c : C) : Function.Injective ((scalar C c).val) :=
  c.val.toLinearEquiv.injective

include hreg in
private theorem nonzero_injective [Nontrivial W] (f : algebra C) (hf : f ≠ 0) :
    Function.Injective f.val := by
  obtain ⟨c, rfl⟩ := exists_scalar C hreg f hf
  exact scalar_injective C c

include hreg in
private theorem centralizing_two_power [Nontrivial W] (g : LinearMap.GeneralLinearGroup (ZMod 2) W)
    (hg : (g : Module.End (ZMod 2) W) ∈ algebra C) (k : ℕ) (hpow : g ^ (2 ^ k) = 1) : g = 1 := by
  let := field C hreg
  let : CharP (algebra C) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (algebra C)).injective 2
  let f : algebra C := ⟨g, hg⟩
  have hp : f ^ (2 ^ k) = 1 := Subtype.ext (congrArg Units.val hpow)
  have hz : (f - 1) ^ (2 ^ k) = 0 := by
    rw [sub_pow_char_pow, hp, one_pow, sub_self]
  have hf : f = 1 := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)
  exact Units.ext (congrArg Subtype.val hf)

private def conjugation (g : LinearMap.GeneralLinearGroup (ZMod 2) W) :
    Module.End (ZMod 2) W ≃ₐ[ZMod 2] Module.End (ZMod 2) W :=
  g.toLinearEquiv.conjAlgEquiv (ZMod 2)

private theorem conjugation_action (g u : LinearMap.GeneralLinearGroup (ZMod 2) W) :
    conjugation g (action u) = action (g * u * g⁻¹) := rfl

omit [IsCyclic C] in
private theorem conjugation_mem (g : LinearMap.GeneralLinearGroup (ZMod 2) W)
    (hg : g ∈ Subgroup.normalizer (C : Set (LinearMap.GeneralLinearGroup (ZMod 2) W)))
    (f : algebra C) :
    conjugation g f.val ∈ algebra C := by
  rintro _ ⟨u, rfl⟩
  have hu : g⁻¹ * u.val * g ∈ C := by
    simpa using (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (C : Set (LinearMap.GeneralLinearGroup (ZMod 2) W))).inv_mem hg)
      u.val).mp u.property
  have hf := f.property _ ⟨⟨g⁻¹ * u.val * g, hu⟩, rfl⟩
  have he := congrArg (conjugation g) hf
  simp only [map_mul] at he
  change conjugation g (action (g⁻¹ * u.val * g)) * _ =
    _ * conjugation g (action (g⁻¹ * u.val * g)) at he
  rw [conjugation_action] at he
  have hcancel : g * (g⁻¹ * u.val * g) * g⁻¹ = u.val := by group
  rw [hcancel] at he
  exact he

variable [Finite W]

private instance algebra_finite : Finite (algebra C) :=
  Finite.of_injective (fun f : algebra C => (f.val : W → W)) (by
    intro f g h
    exact Subtype.ext (LinearMap.ext (congrFun h)))

private def normalizerAut (g : Subgroup.normalizer (C : Set (LinearMap.GeneralLinearGroup (ZMod 2) W))) :
    algebra C ≃ₐ[ZMod 2] algebra C := by
  let f : algebra C →ₐ[ZMod 2] algebra C :=
    ((conjugation g.val).toAlgHom.comp (algebra C).val).codRestrict
      _ (conjugation_mem C g.val g.property)
  apply AlgEquiv.ofBijective f
  apply (Finite.injective_iff_bijective).mp
  intro a b hab
  apply Subtype.ext
  exact (conjugation g.val).injective (congrArg Subtype.val hab)

private def normalizerHom : Subgroup.normalizer (C : Set (LinearMap.GeneralLinearGroup (ZMod 2) W)) →*
    (algebra C ≃ₐ[ZMod 2] algebra C) where
  toFun := normalizerAut C
  map_one' := by ext f : 1; exact Subtype.ext rfl
  map_mul' g h := by ext f : 1; exact Subtype.ext rfl

private theorem kernel_mem (g : Subgroup.normalizer (C : Set (LinearMap.GeneralLinearGroup (ZMod 2) W)))
    (hg : normalizerHom C g = 1) : (g.val : Module.End (ZMod 2) W) ∈ algebra C := by
  rintro _ ⟨c, rfl⟩
  have hf := congrArg (fun e : algebra C ≃ₐ[ZMod 2] algebra C =>
    (e (scalar C c)).val) hg
  change (g.val : Module.End (ZMod 2) W) * (c.val : Module.End (ZMod 2) W) *
    ↑(g.val⁻¹) = ↑c.val at hf
  have hcomm := congrArg (fun e : Module.End (ZMod 2) W => e * (g.val : Module.End (ZMod 2) W)) hf
  simp only [mul_assoc, Units.inv_mul, mul_one] at hcomm
  exact hcomm.symm

include hreg in
/-- Two-subgroups of the normalizer of a regular cyclic group on the nonzero
vectors of a finite binary vector space are cyclic. -/
public theorem isCyclic_of_isPGroup_le_normalizer
    (P : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)) (hP : IsPGroup 2 P)
    (hle : P ≤ Subgroup.normalizer (C : Set (LinearMap.GeneralLinearGroup (ZMod 2) W))) :
    IsCyclic P := by
  cases subsingleton_or_nontrivial W
  · infer_instance
  let := field C hreg
  let f := (normalizerHom C).comp (Subgroup.inclusion hle)
  apply isCyclic_of_injective f
  apply (injective_iff_map_eq_one f).mpr
  intro g hg
  obtain ⟨k, hk⟩ := hP g
  apply Subtype.ext
  exact centralizing_two_power C hreg g.val
    (kernel_mem C (Subgroup.inclusion hle g) hg) k (congrArg Subtype.val hk)

omit [IsCyclic C] in
private theorem normalizerHom_apply_action
    (g : Subgroup.normalizer (C : Set (LinearMap.GeneralLinearGroup (ZMod 2) W)))
    (f : algebra C) (v : W) :
    (normalizerHom C g f).val ((g.val : Module.End (ZMod 2) W) v) =
      (g.val : Module.End (ZMod 2) W) (f.val v) := by
  change g.val.toLinearEquiv
    (f.val (g.val.toLinearEquiv.symm (g.val.toLinearEquiv v))) = _
  rw [g.val.toLinearEquiv.symm_apply_apply]
  rfl

include hreg in
/-- A nonidentity involution normalizing a regular cyclic group fixes at most
the square root of the number of vectors. -/
public theorem fixedSpace_card_sq_le
    (t : LinearMap.GeneralLinearGroup (ZMod 2) W) (ht : t ≠ 1) (ht2 : t ^ 2 = 1)
    (htN : t ∈ Subgroup.normalizer (C : Set (LinearMap.GeneralLinearGroup (ZMod 2) W))) :
    Nat.card (BinaryOffender.fixedSpace (Units.coeHom (Module.End (ZMod 2) W))
      (Subgroup.zpowers t)) ^ 2 ≤ Nat.card W := by
  classical
  cases subsingleton_or_nontrivial W
  · exact (ht (Subsingleton.elim _ _)).elim
  let g : Subgroup.normalizer (C : Set (LinearMap.GeneralLinearGroup (ZMod 2) W)) := ⟨t, htN⟩
  have hne : normalizerHom C g ≠ 1 := by
    intro he
    exact ht (centralizing_two_power C hreg t (kernel_mem C g he) 1 (by simpa using ht2))
  obtain ⟨f, hf⟩ : ∃ f : algebra C, normalizerHom C g f ≠ f := by
    by_contra! hh
    apply hne
    ext f : 1
    exact hh f
  let U := BinaryOffender.fixedSpace (Units.coeHom (Module.End (ZMod 2) W))
    (Subgroup.zpowers t)
  have hfix (u : U) : (t : Module.End (ZMod 2) W) u.val = u.val :=
    u.property ⟨t, Subgroup.mem_zpowers t⟩
  have htrans (v : U) : (normalizerHom C g f).val v.val =
      (t : Module.End (ZMod 2) W) (f.val v.val) := by
    have h := normalizerHom_apply_action C g f v.val
    change (normalizerHom C g f).val ((t : Module.End (ZMod 2) W) v.val) = _ at h
    rw [hfix] at h
    exact h
  have hdis (u v : U) :
      (t : Module.End (ZMod 2) W) (u.val + f.val v.val) - (u.val + f.val v.val) =
        (normalizerHom C g f - f).val v.val := by
    rw [map_add, hfix, ← htrans]
    change u.val + (normalizerHom C g f).val v.val - (u.val + f.val v.val) =
      (normalizerHom C g f).val v.val - f.val v.val
    abel
  let j : U × U → W := fun x => x.1.val + f.val x.2.val
  have hj : Function.Injective j := by
    intro a b hab
    have hd := congrArg (fun w : W => (t : Module.End (ZMod 2) W) w - w) hab
    change (t : Module.End (ZMod 2) W) (a.1.val + f.val a.2.val) -
      (a.1.val + f.val a.2.val) =
      (t : Module.End (ZMod 2) W) (b.1.val + f.val b.2.val) -
      (b.1.val + f.val b.2.val) at hd
    rw [hdis, hdis] at hd
    have h2 : a.2 = b.2 := Subtype.ext
      (nonzero_injective C hreg (normalizerHom C g f - f) (sub_ne_zero.mpr hf) hd)
    apply Prod.ext _ h2
    apply Subtype.ext
    exact add_right_cancel (show a.1.val + f.val b.2.val = b.1.val + f.val b.2.val by
      simpa only [j, h2] using hab)
  simpa only [Nat.card_prod, pow_two] using Nat.card_le_card_of_injective j hj

end Representation.BinarySingerNormalizer
