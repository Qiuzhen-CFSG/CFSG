module

public import Theory.LinearAlgebra.QuadraticHyperplaneStabilizer
public import Theory.Representation.OrthogonalFourPlusMatrix.LowRank
public import Theory.Representation.OrthogonalFourPlusMatrix.InvariantQuadratic
public import Theory.Representation.BinaryOffender.NormalizerExtension
import Mathlib.Tactic.FinCases

/-!
# Small actors in the full determinant normalizer

The eight-dimensional binary determinant module has no nonidentity actor
of displacement rank one. If an elementary subgroup has common fixed
codimension at most two, all its elements are F₄-linear involutions and
preserve the determinant. A nonidentity element has field displacement
rank one. Its fixed hyperplane is the common fixed space, whose pointwise
orthogonal stabilizer consists of that element and the identity. The
elementary subgroup therefore has rank at most one.

This supplies the low-rank branch of the full-normalizer non-FF estimate
for the natural A₅ × A₅ tensor section in Aschbacher–Smith D.3.9,
printed pp.199–200.
-/

@[expose] public noncomputable section
open Module Matrix Subgroup
namespace ClassicalOrthogonal.FourPlusMatrix
variable {K : Type*} [Field K]
theorem determinant_polar_separating :
    (determinantForm (F := K)).polarBilin.SeparatingLeft := by
  intro M h
  have h00 := h !![0,0;0,1]
  have h01 := h !![0,0;1,0]
  have h10 := h !![0,1;0,0]
  have h11 := h !![1,0;0,0]
  simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    determinantForm_apply, Matrix.det_fin_two] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j
  · change M 0 0 = 0
    linear_combination h00
  · change M 0 1 = 0
    linear_combination -h01
  · change M 1 0 = 0
    linear_combination -h10
  · change M 1 1 = 0
    linear_combination h11

namespace Binary
open Representation.BinaryOffender Representation.BinaryOffender.NaturalTensor

theorem normalizer_linearEquiv_mem (t : linearNormalizer action) :
    LinearMap.GeneralLinearGroup.toLinearEquiv t.val ∈ normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)) := by
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V
  have he : (actionImage action).map e.toMonoidHom = linearAction.range := by
    have hg (g : G) : e (action.asGroupHom g) = linearAction g := by
      apply LinearEquiv.ext
      intro v
      exact (linearAction_apply g v).symm
    ext u
    constructor
    · rintro ⟨_,⟨g,rfl⟩,rfl⟩
      exact ⟨g,(hg g).symm⟩
    · rintro ⟨g,rfl⟩
      exact ⟨action.asGroupHom g,⟨g,rfl⟩,hg g⟩
  have hh := (actionImage action).le_normalizer_map e.toMonoidHom
    (Subgroup.mem_map_of_mem e.toMonoidHom t.property)
  rwa [he] at hh

theorem low_rank_involutions_eq_of_fixed
    (t s : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (hs : s ∈ normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (hrt : finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 2)
    (hrs : finrank (ZMod 2) (LinearMap.range (s.toLinearMap - LinearMap.id)) ≤ 2)
    (ht2 : ∀ v, t (t v) = v) (hs2 : ∀ v, s (s v) = v)
    (ht1 : t ≠ 1) (hfix : ∀ v, t v = v → s v = v) : s = 1 ∨ s = t := by
  obtain ⟨t', htt, hrt', _⟩ := low_rank_nonidentity t ht hrt ht1
  obtain ⟨s', hss⟩ := low_rank_field_equiv s hs hrs
  have htp : ∀ v, determinantForm (t' v) = determinantForm v := by
    simpa only [determinantForm_apply] using
      field_involution_preserves_det t' (by rwa [htt])
        (by intro v; simpa only [← htt, LinearEquiv.restrictScalars_apply] using ht2 v)
  have hsp : ∀ v, determinantForm (s' v) = determinantForm v := by
    simpa only [determinantForm_apply] using
      field_involution_preserves_det s' (by rwa [hss])
        (by intro v; simpa only [← hss, LinearEquiv.restrictScalars_apply] using hs2 v)
  have ht1' : t' ≠ 1 := by
    intro hh
    apply ht1
    rw [← htt, hh]
    rfl
  have hfix' : ∀ v, t' v = v → s' v = v := by
    intro v hv
    have h := hfix v (by simpa only [← htt, LinearEquiv.restrictScalars_apply] using hv)
    simpa only [← hss, LinearEquiv.restrictScalars_apply] using h
  rcases QuadraticForm.eq_one_or_eq_of_fixed_rank_one determinantForm
    determinant_polar_separating t' s' htp hsp hrt'.le ht1' hfix' with hh | hh
  · left
    rw [← hss, hh]
    rfl
  · right
    rw [← hss, ← htt, hh]


local instance : Finite (Module.End (ZMod 2) V) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

theorem rank_le_one_of_fixedCodim_le_two
    (A : Subgroup (linearNormalizer action)) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim (normalizerRepresentation action) A ≤ 2) : rank A ≤ 1 := by
  classical
  let := hA.2
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  let et := LinearMap.GeneralLinearGroup.toLinearEquiv t.val
  have htlow : finrank (ZMod 2) (LinearMap.range (et.toLinearMap - LinearMap.id)) ≤ 2 :=
    (operatorFixedCodim_le_fixedCodim (normalizerRepresentation action) A ht).trans hsmall
  have het1 : et ≠ 1 := by
    intro hh
    exact ht1 (Subtype.ext (Units.ext (congrArg LinearEquiv.toLinearMap hh)))
  obtain ⟨_, _, _, hdimt⟩ := low_rank_nonidentity et (normalizer_linearEquiv_mem t) htlow het1
  have hle : fixedSpace (normalizerRepresentation action) A ≤
      LinearMap.ker (t.val.val - 1) := by
    intro v hv
    exact sub_eq_zero.mpr (hv ⟨t,ht⟩)
  have heq : fixedSpace (normalizerRepresentation action) A =
      LinearMap.ker (t.val.val - 1) := by
    apply Submodule.eq_of_le_of_finrank_le hle
    have hh := operatorFixedCodim_add_finrank t.val.val
    have hh' := fixedCodim_add_finrank (normalizerRepresentation action) A
    change operatorFixedCodim t.val.val = 2 at hdimt
    omega
  have hall (s : A) : s.val = 1 ∨ s.val = t := by
    let es := LinearMap.GeneralLinearGroup.toLinearEquiv s.val.val
    have hslow : finrank (ZMod 2) (LinearMap.range (es.toLinearMap - LinearMap.id)) ≤ 2 :=
      (operatorFixedCodim_le_fixedCodim (normalizerRepresentation action) A s.property).trans hsmall
    have ht2 : t * t = 1 := by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) t ht
    have hs2 : s.val * s.val = 1 := by
      simpa only [pow_two] using
        elemPow_eq_one_of_isElementaryAbelian (p := 2) s.val s.property
    have hf (v : V) (hv : et v = v) : es v = v := by
      have hh : v ∈ fixedSpace (normalizerRepresentation action) A := by
        rw [heq]
        exact sub_eq_zero.mpr hv
      exact hh s
    rcases low_rank_involutions_eq_of_fixed et es (normalizer_linearEquiv_mem t)
      (normalizer_linearEquiv_mem s.val) htlow hslow
      (fun v => congrArg (fun u : linearNormalizer action => u.val.val v) ht2)
      (fun v => congrArg (fun u : linearNormalizer action => u.val.val v) hs2)
      het1 hf with hs | hs
    · left
      exact Subtype.ext (Units.ext (congrArg LinearEquiv.toLinearMap hs))
    · right
      exact Subtype.ext (Units.ext (congrArg LinearEquiv.toLinearMap hs))
  let f : Bool → A := fun b => if b then ⟨t,ht⟩ else 1
  have hf : Function.Surjective f := by
    intro s
    rcases hall s with hs | hs
    · refine ⟨false, ?_⟩
      apply Subtype.ext
      exact hs.symm
    · refine ⟨true, ?_⟩
      apply Subtype.ext
      exact hs.symm
  have hc : Nat.card A ≤ 2 := by
    have hb : Nat.card Bool = 2 := by simp
    simpa only [hb] using Nat.card_le_card_of_surjective f hf
  have hh := Nat.log_mono_right (b := 2) hc
  change rank A ≤ Nat.log 2 2 at hh
  exact hh


/-- Every nontrivial subgroup of the full normalizer moves at least two
binary dimensions. -/
theorem fixedCodim_ge_two_of_nontrivial
    (A : Subgroup (linearNormalizer action)) (hA : A ≠ ⊥) :
    2 ≤ fixedCodim (normalizerRepresentation action) A := by
  obtain ⟨t,ht,ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA
  by_contra! hsmall
  let et := LinearMap.GeneralLinearGroup.toLinearEquiv t.val
  have hbound := operatorFixedCodim_le_fixedCodim (normalizerRepresentation action) A ht
  change operatorFixedCodim t.val.val ≤ fixedCodim (normalizerRepresentation action) A at hbound
  have htlow : finrank (ZMod 2) (LinearMap.range (et.toLinearMap - LinearMap.id)) ≤ 2 := by
    change operatorFixedCodim t.val.val ≤ 2
    omega
  have het1 : et ≠ 1 := by
    intro hh
    exact ht1 (Subtype.ext (Units.ext (congrArg LinearEquiv.toLinearMap hh)))
  obtain ⟨_, _, _, hdimt⟩ := low_rank_nonidentity et (normalizer_linearEquiv_mem t) htlow het1
  change operatorFixedCodim t.val.val = 2 at hdimt
  omega

end Binary
end ClassicalOrthogonal.FourPlusMatrix
