module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
The private Hyperbolic section adapts Atlas/LinearAlgebra/SymplecticBasis.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917, via the existing CFSG port
Theory/AtlasPort/LinearAlgebra/SymplecticBasis.lean. Covered by the ATLAS
Research and Attribution License 1.0; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. Changes: module-compatible private implementation,
only the splitting needed for dimension parity, and explicit unused-parameter
removal. The existing non-module port is preserved.
-/

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RepresentationTheory.Invariants

/-!
# Nondegenerate fixed spaces of coprime symplectic actions

Averaging projects onto the invariant subspace and preserves its pairing
with an invariant vector. This proves nondegeneracy of the restricted
alternating form. The existing hyperbolic splitting then proves even
dimension by induction.

This supplies the linear argument in Aschbacher–Smith H.7, printed p.389,
combined manuscript of 1 March 2004. The splitting is reused from the
existing ATLAS port; no representation classification is assumed.
-/

noncomputable section
namespace SymplecticConjugatePair.OddOrder.Hyperbolic
open LinearMap
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (B : LinearMap.BilinForm F V) (hA : B.IsAlt)

/-- Nondegeneracy supplies a normalized partner without a characteristic restriction. -/
theorem exists_partner (hB : B.Nondegenerate) {e : V} (he : e ≠ 0) :
    ∃ f, B e f = 1 := by
  obtain ⟨v,hv⟩ : ∃ v, B e v ≠ 0 := by
    by_contra! h
    exact he (hB.1 e h)
  exact ⟨(B e v)⁻¹ • v, by simp [map_smul, hv]⟩

variable (e f : V) (hef : B e f = 1)

/-- The simultaneous orthogonal complement of the selected hyperbolic pair. -/
def complement : Submodule F V := (B.flip e).ker ⊓ (B.flip f).ker

@[simp] theorem mem_complement (x : V) :
    x ∈ complement B e f ↔ B x e = 0 ∧ B x f = 0 := Iff.rfl

/-- Projection onto the selected plane, in its normalized coordinates. -/
def planeProjection : V →ₗ[F] V := (B.flip f).smulRight e - (B.flip e).smulRight f

@[simp] theorem planeProjection_apply (x : V) :
    planeProjection B e f x = (B x f) • e - (B x e) • f := rfl

include hA hef
theorem reversed_pairing : B f e = -1 := by rw [← hA.neg_eq e f, hef]

@[simp] theorem projection_e : planeProjection B e f e = e := by
  simp [planeProjection_apply, hef, hA.self_eq_zero]

@[simp] theorem projection_f : planeProjection B e f f = f := by
  simp [planeProjection_apply, reversed_pairing B hA e f hef, hA.self_eq_zero]

theorem remainder_mem (x : V) : x - planeProjection B e f x ∈ complement B e f := by
  simp only [mem_complement, planeProjection_apply, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hA.self_eq_zero,
    reversed_pairing B hA e f hef, hef]
  constructor <;> ring

/-- The hyperbolic coordinates plus the actual complement give a direct decomposition. -/
def split : V ≃ₗ[F] (F × F) × complement B e f where
  toFun x := ((B x f, -B x e), ⟨x-planeProjection B e f x, remainder_mem B hA e f hef x⟩)
  invFun z := z.1.1 • e + z.1.2 • f + z.2.val
  left_inv x := by
    simp only [planeProjection_apply, neg_smul]
    abel
  right_inv z := by
    rcases z with ⟨⟨r,s⟩,⟨w,hw⟩⟩
    have hw' := (mem_complement B e f w).mp hw
    apply Prod.ext
    · apply Prod.ext <;>
        simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
          hef, hA.self_eq_zero, reversed_pairing B hA e f hef, hw'.1, hw'.2]
    · apply Subtype.ext
      simp only [planeProjection_apply, map_add, map_smul, hef, hA.self_eq_zero,
        reversed_pairing B hA e f hef, hw'.1, hw'.2]
      simp
  map_add' x y := by
    apply Prod.ext
    · simp [map_add, add_comm]
    · apply Subtype.ext
      change x+y-planeProjection B e f (x+y) =
        (x-planeProjection B e f x)+(y-planeProjection B e f y)
      rw [map_add]
      abel
  map_smul' r x := by
    apply Prod.ext
    · simp [map_smul, mul_neg]
    · apply Subtype.ext
      simp [map_smul, smul_sub]

omit hef in
/-- The alternating restriction on the actual complement. -/
theorem complement_alternating : (B.restrict (complement B e f)).IsAlt := by
  intro x
  exact hA.self_eq_zero x.val

/-- Nondegeneracy survives hyperbolic splitting. -/
theorem complement_nondegenerate (hB : B.Nondegenerate) :
    (B.restrict (complement B e f)).Nondegenerate := by
  have hs : (B.restrict (complement B e f)).SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    apply hB.1 x.val
    intro y
    obtain ⟨z,rfl⟩ := (split B hA e f hef).symm.surjective y
    rcases z with ⟨⟨r,s⟩,w⟩
    have hp := x.prop
    have hz : B x.val w.val = 0 := hx w
    change B x.val (r • e + s • f + w.val) = 0
    simp [map_add, map_smul, (mem_complement B e f x.val).mp hp, hz]
  refine ⟨hs, ?_⟩
  intro x hx
  apply hs x
  intro y
  change B x.val y.val = 0
  rw [← hA.neg_eq y.val x.val]
  change -((B.restrict (complement B e f)) y x) = 0
  rw [hx y, neg_zero]

theorem finrank_complement [FiniteDimensional F V] :
    Module.finrank F (complement B e f) + 2 = Module.finrank F V := by
  have h := (split B hA e f hef).finrank_eq
  simpa [Module.finrank_prod, Module.finrank_self, Nat.add_comm] using h.symm



end SymplecticConjugatePair.OddOrder.Hyperbolic
end

public section

namespace SymplecticConjugatePair.OddOrder
open Module Representation
universe u v

/-- Hyperbolic splitting forces even dimension for a nondegenerate alternating form. -/
theorem even_finrank_of_nondegenerate {F : Type v} [Field F] {V : Type u} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (B : LinearMap.BilinForm F V) (hA : B.IsAlt) (hB : B.Nondegenerate) :
    Even (finrank F V) := by
  suffices ∀ d : ℕ, ∀ (W : Type u) [AddCommGroup W] [Module F W]
      [FiniteDimensional F W], ∀ (C : LinearMap.BilinForm F W), C.IsAlt → C.Nondegenerate →
      finrank F W = d → Even d from this _ V B hA hB rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro W _ _ _ C hC hn hd
    by_cases hz : d = 0
    · simp [hz]
    have hp : 0 < finrank F W := by omega
    obtain ⟨e, he⟩ := finrank_pos_iff_exists_ne_zero.mp hp
    obtain ⟨f, hf⟩ := Hyperbolic.exists_partner C hn he
    have hdim := Hyperbolic.finrank_complement C hC e f hf
    have heven := ih (finrank F (Hyperbolic.complement C e f)) (by omega)
      (Hyperbolic.complement C e f) (C.restrict _)
      (Hyperbolic.complement_alternating C hC e f)
      (Hyperbolic.complement_nondegenerate C hC e f hf hn) rfl
    obtain ⟨k, hk⟩ := heven
    exact ⟨k+1, by omega⟩

/-- Averaging preserves pairing with invariant vectors, so the invariant space
of an action of invertible order is nondegenerate. -/
theorem invariants_nondegenerate {F G V : Type*} [Field F] [Group G] [Fintype G]
    [AddCommGroup V] [Module F V] [Invertible (Fintype.card G : F)]
    (ρ : Representation F G V) (B : LinearMap.BilinForm F V) (hA : B.IsAlt)
    (hB : B.Nondegenerate) (hpres : ∀ g x y, B (ρ g x) (ρ g y) = B x y) :
    (B.restrict ρ.invariants).Nondegenerate := by
  have hl : (B.restrict ρ.invariants).SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    apply hB.1 x.val
    intro y
    have hxy : ∀ g : G, B x.val (ρ g y) = B x.val y := by
      intro g
      simpa only [x.property g] using hpres g x.val y
    have ha : B x.val (ρ.averageMap y) = B x.val y := by
      simp only [averageMap, GroupAlgebra.average, map_smul, map_sum, asAlgebraHom_of,
        LinearMap.smul_apply, LinearMap.sum_apply, hxy, Finset.sum_const,
        Finset.card_univ, smul_eq_mul, nsmul_eq_mul, invOf_mul_cancel_left]
    exact ha.symm.trans (hx ⟨_, ρ.averageMap_invariant y⟩)
  refine ⟨hl, ?_⟩
  intro x hx
  apply hl x
  intro y
  exact hA.eq_iff.mpr (hx y)

end SymplecticConjugatePair.OddOrder
