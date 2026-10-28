/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Elementary
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Geometry
public import Mathlib.LinearAlgebra.Reflection
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.Tactic.FieldSimp

/-!
# Reflections and singular connectors in every characteristic

Adapted from `Atlas/LinearAlgebra/Quadratic{Hyperbolic,Reflection,Transitivity,
EqualValue,ComplementWitness}.lean` and
`Atlas/LinearGroups/Orthogonal/{Basic,ReflectionGroup,IsometryTransport}.lean`.
We reuse CFSG's forms, Siegel transformations and isometry point group. A
quadratic reflection uses the unhalved polar form, and orthogonal singular
vectors have a singular connector even over the binary field. These are the
local ingredients of the hyperbolic-pair induction. Only the needed formulas
and transport are retained; determinant and line-extension machinery is omitted.
Namespaces, public module boundaries and imports are adapted for Lean 4.33.
-/

@[expose] public noncomputable section
universe u
open Theory.AlgebraicGroup

namespace ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- Completing a normalized partner to a singular one uses no factor of 1/2. -/
theorem partner_correction (u f : V) (hu : Q u = 0)
    (huf : Q.polarBilin u f = 1) :
    Q (f - Q f • u) = 0 ∧ Q.polarBilin u (f - Q f • u) = 1 := by
  have hfu : Q.polarBilin f u = 1 := (polar_swap Q f u).trans huf
  have huu : Q.polarBilin u u = 0 := by rw [polar_self, hu, mul_zero]
  constructor
  · rw [sub_eq_add_neg, ← neg_smul, add_smul, hu, hfu]
    ring
  · rw [map_sub, map_smul, huu, smul_zero, sub_zero, huf]

/-- Any vector outside the polar radical has a partner of pairing one. -/
theorem exists_normalized_partner (u : V)
    (hu : ¬ ∀ w, Q.polarBilin u w = 0) : ∃ f, Q.polarBilin u f = 1 := by
  classical
  obtain ⟨w,hw⟩ := not_forall.mp hu
  refine ⟨(Q.polarBilin u w)⁻¹ • w, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hw]


end ClassicalOrthogonal.Quadratic

namespace ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

def reflectionFunctional (a : V) : V →ₗ[F] F := (Q a)⁻¹ • Q.polarBilin.flip a

theorem reflectionFunctional_self (a : V) (ha : Q a ≠ 0) :
    reflectionFunctional Q a a = 2 := by
  change (Q a)⁻¹ * Q.polarBilin a a = 2
  rw [polar_self]
  field_simp

/-- The existing linear reflection, normalized using the quadratic value. -/
def reflectionLinear (a : V) (ha : Q a ≠ 0) : V ≃ₗ[F] V :=
  Module.reflection (reflectionFunctional_self Q a ha)

@[simp] theorem reflectionLinear_apply (a : V) (ha : Q a ≠ 0) (x : V) :
    reflectionLinear Q a ha x = x - ((Q a)⁻¹ * Q.polarBilin x a) • a :=
  Module.reflection_apply _ _

theorem reflection_preserves (a : V) (ha : Q a ≠ 0) (x : V) :
    Q (reflectionLinear Q a ha x) = Q x := by
  rw [reflectionLinear_apply,sub_eq_add_neg,← neg_smul,add_smul]
  field_simp
  ring

def reflectionIsometry (a : V) (ha : Q a ≠ 0) : Q.IsometryEquiv Q where
  __ := reflectionLinear Q a ha
  map_app' := reflection_preserves Q a ha

theorem sub_singular_value (u v : V) (hu : Q u=0) (hv : Q v=0) :
    Q (u-v) = -Q.polarBilin u v := by
  rw [sub_eq_add_neg,← neg_one_smul F v,add_smul,hu,hv]
  ring


end ClassicalOrthogonal.Quadratic

namespace ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

theorem singular_not_polar_radical (hQ : Q.radical=⊥) (u : V) (hu : u≠0)
    (hqu : Q u=0) : ¬ ∀ w, Q.polarBilin u w=0 := by
  intro h
  have hm : u ∈ Q.radical := ⟨hqu,LinearMap.ext h⟩
  rw [hQ,Submodule.mem_bot] at hm
  exact hu hm

/-- Two nonzero linear pairings admit a common nonzero value, even over F₂. -/
theorem exists_pairing_both (u v : V)
    (hu : ¬ ∀ w, Q.polarBilin u w=0) (hv : ¬ ∀ w, Q.polarBilin v w=0) :
    ∃ w, Q.polarBilin u w≠0 ∧ Q.polarBilin v w≠0 := by
  obtain ⟨a,ha⟩ := exists_normalized_partner Q u hu
  obtain ⟨b,hb⟩ := exists_normalized_partner Q v hv
  by_cases hva : Q.polarBilin v a=0
  · by_cases hub : Q.polarBilin u b=0
    · refine ⟨a+b,?_,?_⟩ <;> simp only [map_add,ha,hb,hva,hub,zero_add,add_zero,ne_eq,one_ne_zero,not_false_eq_true]
    · exact ⟨b,hub,hb ▸ one_ne_zero⟩
  · exact ⟨a,ha ▸ one_ne_zero,hva⟩

/-- Orthogonal singular vectors have a singular connector pairing nontrivially with both. -/
theorem exists_singular_connector (u v : V) (hqu : Q u=0)
    (huv : Q.polarBilin u v=0)
    (hu : ¬ ∀ w, Q.polarBilin u w=0) (hv : ¬ ∀ w, Q.polarBilin v w=0) :
    ∃ w, Q w=0 ∧ Q.polarBilin u w≠0 ∧ Q.polarBilin v w≠0 := by
  obtain ⟨w,huw,hvw⟩ := exists_pairing_both Q u v hu hv
  have hvu : Q.polarBilin v u=0 := (polar_swap Q v u).trans huv
  have huu : Q.polarBilin u u=0 := by rw [polar_self,hqu,mul_zero]
  refine ⟨w-(Q w / Q.polarBilin u w) • u, ?_, ?_, ?_⟩
  · rw [sub_eq_add_neg,← neg_smul,add_smul,hqu,polar_swap Q w u]
    field_simp
    ring
  · simpa only [map_sub,map_smul,huu,smul_zero,sub_zero] using huw
  · simpa only [map_sub,map_smul,hvu,smul_zero,sub_zero] using hvw


end ClassicalOrthogonal.Quadratic

namespace ClassicalOrthogonal.Quadratic
variable {F V W : Type u} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
variable (Q : QuadraticForm F V) (R : QuadraticForm F W)

theorem sub_value (u v : V) : Q (u-v) = Q u + Q v - Q.polarBilin u v := by
  rw [sub_eq_add_neg, ← neg_one_smul F v, add_smul]
  ring

/-- An actual quadratic isometry transports the unhalved polar form. -/
theorem isometry_between_polar (g : Q.IsometryEquiv R) (x y : V) :
    R.polarBilin (g x) (g y) = Q.polarBilin x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, g.map_app]


end ClassicalOrthogonal.Quadratic

namespace ClassicalOrthogonal.ReflectionGeneration
open ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- The existing point group and the quadratic isometry structure have the same carrier. -/
def isometryCarrierEquiv : quadraticIsometrySubgroup Q ≃ Q.IsometryEquiv Q where
  toFun g := { g.val with map_app' := (mem_quadraticIsometrySubgroup Q g.val).mp g.prop }
  invFun g := ⟨g.toLinearEquiv, (mem_quadraticIsometrySubgroup Q _).mpr g.map_app⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem isometry_preserves (g : quadraticIsometrySubgroup Q) (v : V) :
    Q (g.val v) = Q v := (mem_quadraticIsometrySubgroup Q g.val).mp g.prop v

/-- Reflection in a vector with nonzero quadratic value, including characteristic two. -/
def reflectionElement (a : V) (ha : Q a ≠ 0) : quadraticIsometrySubgroup Q :=
  (isometryCarrierEquiv Q).symm (reflectionIsometry Q a ha)

/-- The subgroup generated by all actual nonsingular reflections. -/
def reflectionSubgroup : Subgroup (quadraticIsometrySubgroup Q) :=
  Subgroup.closure {g | ∃ a ha, g = reflectionElement Q a ha}

theorem reflectionElement_mem (a : V) (ha : Q a ≠ 0) :
    reflectionElement Q a ha ∈ reflectionSubgroup Q := Subgroup.subset_closure ⟨a, ha, rfl⟩

end ClassicalOrthogonal.ReflectionGeneration

namespace ClassicalOrthogonal.ReflectionGeneration
variable {F V W : Type u} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
variable {Q : QuadraticForm F V} {R : QuadraticForm F W}

/-- Conjugation transports the full isometry group, preserving its multiplication. -/
def isometryGroupTransport (g : Q.IsometryEquiv R) : quadraticIsometrySubgroup Q ≃* quadraticIsometrySubgroup R where
  toFun k := (isometryCarrierEquiv R).symm
    ((g.symm.trans (isometryCarrierEquiv Q k)).trans g)
  invFun k := (isometryCarrierEquiv Q).symm
    ((g.trans (isometryCarrierEquiv R k)).trans g.symm)
  left_inv k := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change g.symm (g (k.val (g.symm (g x)))) = k.val x
    rw [g.symm_apply_apply, g.symm_apply_apply]
  right_inv k := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change g (g.symm (k.val (g (g.symm x)))) = k.val x
    rw [g.apply_symm_apply, g.apply_symm_apply]
  map_mul' k l := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change g (k.val (l.val (g.symm x))) = g (k.val (g.symm (g (l.val (g.symm x)))))
    rw [g.symm_apply_apply]

end ClassicalOrthogonal.ReflectionGeneration
