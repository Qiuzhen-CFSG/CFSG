/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.Basic

/-!
# Splitting off and fixing a hyperbolic plane

Adapted from `Atlas/LinearAlgebra/Quadratic{Split,ComplementTransport,
ComplementExtension,ComplementWitness}.lean`. The explicit plane projection
splits the whole quadratic form. Isometries of its perpendicular complement
extend by the identity on the plane. We retain restriction and extension,
without the unrelated Witt-index witnesses or transitivity results, and adapt
namespaces and public boundaries for CFSG / Lean 4.33.
-/

@[expose] public noncomputable section
universe u
open Theory.AlgebraicGroup

namespace ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (e f : V)

def complement : Submodule F V := (Q.polarBilin.flip e).ker ⊓ (Q.polarBilin.flip f).ker

@[simp] theorem mem_complement (x : V) :
    x ∈ complement Q e f ↔ Q.polarBilin x e = 0 ∧ Q.polarBilin x f = 0 := Iff.rfl

def planeProjection : V →ₗ[F] V :=
  (Q.polarBilin.flip f).smulRight e + (Q.polarBilin.flip e).smulRight f

@[simp] theorem planeProjection_apply (x : V) :
    planeProjection Q e f x = Q.polarBilin x f • e + Q.polarBilin x e • f := rfl

variable (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)

include he hf hef in
theorem remainder_mem (x : V) : x - planeProjection Q e f x ∈ complement Q e f := by
  have hee : Q.polarBilin e e = 0 := by rw [polar_self,he,mul_zero]
  have hff : Q.polarBilin f f = 0 := by rw [polar_self,hf,mul_zero]
  have hfe : Q.polarBilin f e = 1 := (polar_swap Q f e).trans hef
  simp only [mem_complement,planeProjection_apply,map_sub,map_add,map_smul,
    LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,
    hee,hff,hef,hfe]
  constructor <;> ring

/-- Actual linear coordinates on the chosen plane and its perpendicular complement. -/
def split : V ≃ₗ[F] (F × F) × complement Q e f where
  toFun x := ((Q.polarBilin x f,Q.polarBilin x e),
    ⟨x-planeProjection Q e f x,remainder_mem Q e f he hf hef x⟩)
  invFun z := z.1.1 • e + z.1.2 • f + z.2.val
  left_inv x := by simp only [planeProjection_apply]; module
  right_inv z := by
    rcases z with ⟨⟨r,s⟩,⟨w,hw⟩⟩
    have hw := (mem_complement Q e f w).mp hw
    have hee : Q.polarBilin e e = 0 := by rw [polar_self,he,mul_zero]
    have hff : Q.polarBilin f f = 0 := by rw [polar_self,hf,mul_zero]
    have hfe : Q.polarBilin f e = 1 := (polar_swap Q f e).trans hef
    apply Prod.ext
    · apply Prod.ext <;>
        simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
          smul_eq_mul,hee,hff,hef,hfe,hw.1,hw.2,mul_zero,mul_one,zero_add,add_zero]
    · apply Subtype.ext
      simp only [planeProjection_apply,map_add,map_smul,hee,hff,hef,hfe,hw.1,hw.2]
      module
  map_add' x y := by
    apply Prod.ext
    · simp only [map_add,LinearMap.add_apply,Prod.mk_add_mk]
    · apply Subtype.ext
      change x+y-planeProjection Q e f (x+y) =
        (x-planeProjection Q e f x)+(y-planeProjection Q e f y)
      rw [map_add]
      module
  map_smul' a x := by
    apply Prod.ext
    · simp only [map_smul,LinearMap.smul_apply,Prod.smul_mk,RingHom.id_apply]
    · apply Subtype.ext
      change a • x-planeProjection Q e f (a • x) = a • (x-planeProjection Q e f x)
      rw [map_smul,smul_sub]

include he hf hef in
/-- Splitting off a hyperbolic pair drops the vector-space dimension by two. -/
theorem finrank_complement [FiniteDimensional F V] :
    Module.finrank F (complement Q e f) + 2 = Module.finrank F V := by
  have h := (split Q e f he hf hef).finrank_eq
  simpa [Module.finrank_prod,Module.finrank_self,Nat.add_comm] using h.symm

/-- The splitting preserves the complete quadratic form, in arbitrary characteristic. -/
theorem split_form (t : (F × F) × complement Q e f) :
    Q ((split Q e f he hf hef).symm t) = t.1.1 * t.1.2 + Q t.2.val := by
  rcases t with ⟨⟨r,s⟩,⟨w,hw⟩⟩
  have hw := (mem_complement Q e f w).mp hw
  have hew : Q.polarBilin e w = 0 := (polar_swap Q e w).trans hw.1
  have hfw : Q.polarBilin f w = 0 := (polar_swap Q f w).trans hw.2
  change Q (r • e + s • f + w) = r*s + Q w
  rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q]
  change Q (r • e) + Q (s • f) + Q.polarBilin (r • e) (s • f) + Q w +
    Q.polarBilin (r • e + s • f) w = _
  simp only [Q.map_smul,map_smul,map_add,LinearMap.add_apply,LinearMap.smul_apply,
    smul_eq_mul,he,hf,hef,hew,hfw]
  ring

/-- Quadratic value in the coordinates of a chosen hyperbolic pair. -/
theorem form_split (x : V) :
    Q x = (split Q e f he hf hef x).1.1 * (split Q e f he hf hef x).1.2 +
      Q (split Q e f he hf hef x).2.val := by
  simpa only [LinearEquiv.symm_apply_apply] using
    split_form Q e f he hf hef (split Q e f he hf hef x)

end ClassicalOrthogonal.Quadratic


namespace ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

def complementForm (e f : V) : QuadraticForm F (complement Q e f) :=
  Q.comp (complement Q e f).subtype

/-- Restrict an ambient isometry carrying one marked pair to another. -/
def complementTransport (g : Q.IsometryEquiv Q) (e f u v : V)
    (he : g e = u) (hf : g f = v) :
    (complementForm Q e f).IsometryEquiv (complementForm Q u v) where
  toFun x := ⟨g x.val, by
    change Q.polarBilin (g x.val) u = 0 ∧ Q.polarBilin (g x.val) v = 0
    rw [← he, ← hf, isometry_polar, isometry_polar]
    exact x.prop⟩
  invFun x := ⟨g.symm x.val, by
    change Q.polarBilin (g.symm x.val) e = 0 ∧ Q.polarBilin (g.symm x.val) f = 0
    have he' : g.symm u = e := by rw [← he, g.symm_apply_apply]
    have hf' : g.symm v = f := by rw [← hf, g.symm_apply_apply]
    rw [← he', ← hf', isometry_polar, isometry_polar]
    exact x.prop⟩
  left_inv x := Subtype.ext (g.symm_apply_apply x.val)
  right_inv x := Subtype.ext (g.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add g x.val y.val)
  map_smul' a x := Subtype.ext (map_smul g a x.val)
  map_app' x := g.map_app x.val


end ClassicalOrthogonal.Quadratic

namespace ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (e f : V)
variable (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)

def complementExtensionLinear
    (k : (complementForm Q e f).IsometryEquiv (complementForm Q e f)) : V ≃ₗ[F] V :=
  (split Q e f he hf hef).trans
    (((LinearEquiv.refl F (F × F)).prodCongr k.toLinearEquiv).trans
      (split Q e f he hf hef).symm)

theorem complementExtension_preserves
    (k : (complementForm Q e f).IsometryEquiv (complementForm Q e f)) (x : V) :
    Q (complementExtensionLinear Q e f he hf hef k x) = Q x := by
  change Q ((split Q e f he hf hef).symm
    ((split Q e f he hf hef x).1, k (split Q e f he hf hef x).2)) = Q x
  rw [split_form, form_split Q e f he hf hef x]
  have hk := k.map_app (split Q e f he hf hef x).2
  change Q (k (split Q e f he hf hef x).2).val = Q (split Q e f he hf hef x).2.val at hk
  exact congrArg (_ + ·) hk

/-- Extension uses the actual quadratic direct sum, with no dimension-only identification. -/
def complementExtension
    (k : (complementForm Q e f).IsometryEquiv (complementForm Q e f)) : Q.IsometryEquiv Q where
  __ := complementExtensionLinear Q e f he hf hef k
  map_app' := complementExtension_preserves Q e f he hf hef k

include he hf hef in
theorem split_e : split Q e f he hf hef e = ((1, 0), 0) := by
  have hee : Q.polarBilin e e = 0 := by rw [polar_self, he, mul_zero]
  apply Prod.ext
  · exact Prod.ext hef hee
  · apply Subtype.ext
    change e - (Q.polarBilin e f • e + Q.polarBilin e e • f) = 0
    rw [hef, hee, one_smul, zero_smul, add_zero, sub_self]

include he hf hef in
theorem split_f : split Q e f he hf hef f = ((0, 1), 0) := by
  have hff : Q.polarBilin f f = 0 := by rw [polar_self, hf, mul_zero]
  have hfe : Q.polarBilin f e = 1 := (polar_swap Q f e).trans hef
  apply Prod.ext
  · exact Prod.ext hff hfe
  · apply Subtype.ext
    change f - (Q.polarBilin f f • e + Q.polarBilin f e • f) = 0
    rw [hff, hfe, zero_smul, one_smul, zero_add, sub_self]

include he hf hef in
theorem split_complement (x : complement Q e f) :
    split Q e f he hf hef x.val = ((0, 0), x) := by
  apply Prod.ext
  · exact Prod.ext x.prop.2 x.prop.1
  · apply Subtype.ext
    change x.val - (Q.polarBilin x.val f • e + Q.polarBilin x.val e • f) = x.val
    have hx := (mem_complement Q e f x.val).mp x.prop
    rw [hx.1, hx.2, zero_smul, zero_smul, add_zero, sub_zero]

theorem complementExtension_fix_e
    (k : (complementForm Q e f).IsometryEquiv (complementForm Q e f)) :
    complementExtension Q e f he hf hef k e = e := by
  change (split Q e f he hf hef).symm
    ((split Q e f he hf hef e).1, k (split Q e f he hf hef e).2) = e
  rw [split_e]
  simp only [map_zero]
  change (1 : F) • e + (0 : F) • f + (0 : V) = e
  simp

theorem complementExtension_fix_f
    (k : (complementForm Q e f).IsometryEquiv (complementForm Q e f)) :
    complementExtension Q e f he hf hef k f = f := by
  change (split Q e f he hf hef).symm
    ((split Q e f he hf hef f).1, k (split Q e f he hf hef f).2) = f
  rw [split_f]
  simp only [map_zero]
  change (0 : F) • e + (1 : F) • f + (0 : V) = f
  simp

theorem complementExtension_apply
    (k : (complementForm Q e f).IsometryEquiv (complementForm Q e f))
    (x : complement Q e f) : complementExtension Q e f he hf hef k x.val = (k x).val := by
  change (split Q e f he hf hef).symm
    ((split Q e f he hf hef x.val).1, k (split Q e f he hf hef x.val).2) = (k x).val
  rw [split_complement]
  change (0 : F) • e + (0 : F) • f + (k x).val = (k x).val
  simp

end ClassicalOrthogonal.Quadratic

namespace ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

theorem complementForm_polar (e f : V) (x y : complement Q e f) :
    (complementForm Q e f).polarBilin x y = Q.polarBilin x.val y.val := by
  rw [complementForm, QuadraticMap.polarBilin_comp]
  rfl


end ClassicalOrthogonal.Quadratic
