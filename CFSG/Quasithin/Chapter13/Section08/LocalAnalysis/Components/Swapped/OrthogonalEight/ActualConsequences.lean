module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.OrthogonalEight.MatrixConsequences
public import Theory.Representation.OrthogonalFourPlusMatrix.Comparison
public import Theory.Representation.OrthogonalFourPlusMatrix.QuadraticActors

/-!
# Actual Ω₄⁺(4) consequences

The determinant module is identified with the natural binary module of the
existing projective elementary orthogonal carrier by an explicit multiplicative
equivalence.  This file transports the rank, quadratic-actor, and normalizer
calculations to that carrier.  In particular, no semilinear description of an
ambient normalizer is used.

Source: Aschbacher–Smith, 13.8.16(1), printed pp.952–953 (PDF pp.969–970).
-/

public section
open Representation.BinaryOffender
open ClassicalOrthogonal
open ClassicalOrthogonal.FourPlusMatrix

namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.OrthogonalEight

/-! ## Transport to the actual carrier -/

theorem binaryCoordinates_equivariant (g : G) (v : V) :
    Binary.binaryCoordinates (action g v) =
      Binary.action (Binary.orthogonalEquiv.symm g)
        (Binary.binaryCoordinates v) := by
  change Binary.binaryCoordinates
    (ClassicalOrthogonal.projectiveElementaryNatural
      (ClassicalOrthogonal.formD 2 F) g v) = _
  simpa using
    (Binary.binaryCoordinates_projective_equivariant
      (Binary.orthogonalEquiv.symm g) v)

theorem displacement_rank_four (g : G) (hg : g ≠ 1) :
    4 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (action g - LinearMap.id)) := by
  let f : G →* Binary.G := Binary.orthogonalEquiv.symm.toMonoidHom
  let e : V ≃ₗ[ZMod 2] Binary.V := Binary.binaryCoordinates
  have he : ∀ x v, e (action x v) = Binary.action (f x) (e v) := by
    intro x v
    change Binary.binaryCoordinates
      (ClassicalOrthogonal.projectiveElementaryNatural
        (ClassicalOrthogonal.formD 2 F) x v) = _
    simpa [f, Binary.orthogonalEquiv] using
      (Binary.binaryCoordinates_projective_equivariant (f x) v)
  have hfg : f g ≠ 1 := by
    intro h
    apply hg
    change Binary.orthogonalEquiv.symm g = 1 at h
    have h' := congrArg Binary.orthogonalEquiv h
    simpa using h'
  exact MatrixConsequences.displacement_rank_eq action f e he g |>.symm ▸
    Displacement.displacement_rank_four (f g) hfg

/-! The preceding result is stronger than the involution case used in 13.8.16. -/
theorem displacement_rank_four_of_involution (g : G) (hg : g ≠ 1)
    (_horder : g ^ 2 = 1) :
    4 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (action g - LinearMap.id)) :=
  displacement_rank_four g hg

theorem actual_quadratic_actor_card_four [Finite G] (A : Subgroup G)
    (hne : A ≠ ⊥) (hA : IsElementaryAbelian 2 A)
    (hq : IsQuadratic action A) (hbound : fixedCodim action A ≤ 2 * rank A) :
    Nat.card A = 4 ∧ fixedCodim action A = 4 := by
  let e : G →* Binary.G := Binary.orthogonalEquiv.symm.toMonoidHom
  let A' : Subgroup Binary.G := A.map e
  let _ : IsElementaryAbelian 2 A := hA
  have heinj : Function.Injective e := Binary.orthogonalEquiv.symm.injective
  have hA' : IsElementaryAbelian 2 A' := by
    exact IsElementaryAbelian.map e
  have he : ∀ x v, Binary.binaryCoordinates (action x v) =
      Binary.action (e x) (Binary.binaryCoordinates v) := by
    intro x v
    change Binary.binaryCoordinates
      (ClassicalOrthogonal.projectiveElementaryNatural
        (ClassicalOrthogonal.formD 2 F) x v) = _
    simpa [e, Binary.orthogonalEquiv] using
      (Binary.binaryCoordinates_projective_equivariant (e x) v)
  have hq' : IsQuadratic Binary.action A' := by
    intro a ha b hb v
    rcases ha with ⟨a0, ha0, rfl⟩
    rcases hb with ⟨b0, hb0, rfl⟩
    have hh := hq a0 ha0 b0 hb0 (Binary.binaryCoordinates.symm v)
    have hh' := congrArg Binary.binaryCoordinates hh
    simpa only [map_sub, he, Binary.binaryCoordinates.apply_symm_apply] using hh'
  have hc' : Nat.card A' ≤ 4 :=
    ClassicalOrthogonal.FourPlusMatrix.QuadraticActors.card_le_four A' hA' hq'
  have hc : Nat.card A ≤ 4 := by
    rw [Nat.card_congr
      (Subgroup.equivMapOfInjective A e heinj).toEquiv]
    change Nat.card A' ≤ 4 at hc'
    exact hc'
  exact quadratic_actor_card_four action finrank_binary A hne hq
    (fun a _ ha => displacement_rank_four a ha) hc hbound

theorem actual_quadratic_actor_card_four_of_elementaryTwo [Finite G]
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hq : IsQuadratic action A) (hbound : fixedCodim action A ≤ 2 * rank A) :
    Nat.card A = 4 ∧ fixedCodim action A = 4 :=
  actual_quadratic_actor_card_four A hA.1 hA.2 hq hbound

/-! ## Normalizers -/

theorem normalizer_no_transvection (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ Subgroup.normalizer
      (linearAction.range : Set (V ≃ₗ[ZMod 2] V))) :
    Module.finrank (ZMod 2)
      (LinearMap.range (t.toLinearMap - LinearMap.id)) ≠ 1 := by
  apply Representation.BinaryNormalizerRank.normalizer_no_rank_one
    linearAction.range (t := t) (hn := ht)
  · rintro _ ⟨g, rfl⟩ hg
    have hg1 : g ≠ 1 := by
      intro he
      apply hg
      rw [he, map_one]
    exact (by decide : 3 ≤ 4).trans (displacement_rank_four g hg1)
  · intro v hv
    have hzero : Binary.binaryCoordinates v = 0 := by
      apply Displacement.common_fixed_eq_zero
      intro gd
      let g : G := Binary.orthogonalEquiv gd
      have h := hv (linearAction g) ⟨g, rfl⟩
      have h' := congrArg Binary.binaryCoordinates h
      change Binary.binaryCoordinates (action g v) = Binary.binaryCoordinates v at h'
      change Binary.binaryCoordinates
        (ClassicalOrthogonal.projectiveElementaryNatural
          (ClassicalOrthogonal.formD 2 F) (Binary.orthogonalEquiv gd) v) =
        Binary.binaryCoordinates v at h'
      have he' := Binary.binaryCoordinates_projective_equivariant gd v
      rw [he'] at h'
      exact h'
    apply Binary.binaryCoordinates.injective
    simpa using hzero

/-! A normal determinant-model subgroup also gives the source-compatible
extension statement for the actual orthogonal carrier. -/
theorem equivariant_extension_no_transvection {H W : Type*} [Group H]
    [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : H →* (W ≃ₗ[ZMod 2] W)) (N : Subgroup H) [N.Normal]
    (f : N ≃* G) (e : W ≃ₗ[ZMod 2] V)
    (he : ∀ n : N, ∀ w, e (ρ n w) = action (f n) (e w)) (h : H) :
    Module.finrank (ZMod 2)
      (LinearMap.range ((ρ h).toLinearMap - LinearMap.id)) ≠ 1 := by
  let f' : N ≃* Binary.G := f.trans Binary.orthogonalEquiv.symm
  let e' : W ≃ₗ[ZMod 2] Binary.V := e.trans Binary.binaryCoordinates
  have he' : ∀ n : N, ∀ w, e' (ρ n w) = Binary.action (f' n) (e' w) := by
    intro n w
    change Binary.binaryCoordinates (e (ρ n w)) = _
    rw [he]
    change Binary.binaryCoordinates
      (ClassicalOrthogonal.projectiveElementaryNatural
        (ClassicalOrthogonal.formD 2 F) (f n) (e w)) = _
    have hh := Binary.binaryCoordinates_projective_equivariant
      (Binary.orthogonalEquiv.symm (f n)) (e w)
    simpa [f', e'] using hh
  exact MatrixConsequences.equivariant_extension_no_transvection ρ N f' e' he' h

/-! ## Critical-line obstruction -/

theorem no_critical_line_of_actual_model {H W : Type*} [Group H]
    [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (f : H →* G)
    (e : W ≃ₗ[ZMod 2] V)
    (he : ∀ g w, e (ρ g w) = action (f g) (e w)) (g : H)
    (hg : f g ≠ 1) (D S : Submodule (ZMod 2) W)
    (hD : Module.finrank (ZMod 2) (W ⧸ D) ≤ 2)
    (hS : Module.finrank (ZMod 2) S ≤ 1) :
    ¬ ∀ d ∈ D, ρ g d - d ∈ S := by
  exact no_critical_line_of_equivariant_rank ρ f e he g
    (displacement_rank_four (f g) hg) D S hD hS

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.OrthogonalEight
