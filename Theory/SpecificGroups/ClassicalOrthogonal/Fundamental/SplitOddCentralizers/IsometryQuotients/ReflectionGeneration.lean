/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Abel

/-!
# Reflection generation in odd characteristic

A nondegenerate quadratic line splits off. An isometry can be adjusted by one
or two reflections to fix that line, then restricted to its perpendicular
space. Induction on dimension proves Cartan–Dieudonné generation on the
actual `quadraticIsometrySubgroup` carrier, including dimension three.

Adapted from `Atlas/LinearAlgebra/QuadraticAnisotropicSplit.lean`,
`QuadraticLineExtension.lean`, `QuadraticEqualValue.lean`, and
`Atlas/LinearGroups/Orthogonal/ReflectionGroup.lean`, `ReflectionGeneration.lean`.
We reuse CFSG's forms and reflections, adapt subgroup membership proofs and
module boundaries for Lean 4.33, and retain only the needed transport lemma.
Source: GLS3 §2.7, the full isometry quotient used in A.2.17, printed p.39.
-/

@[expose] public noncomputable section
universe u
open Theory.AlgebraicGroup
namespace ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (a : V)

abbrev linePerp : Submodule F V := (Q.polarBilin.flip a).ker

def lineCoordinate : V →ₗ[F] F := (Q.polarBilin a a)⁻¹ • Q.polarBilin.flip a

variable (ha : Q.polarBilin a a ≠ 0)

include ha in
theorem lineCoordinate_self : lineCoordinate Q a a = 1 := inv_mul_cancel₀ ha

theorem lineCoordinate_perp (x : linePerp Q a) : lineCoordinate Q a x.val = 0 := by
  change (Q.polarBilin a a)⁻¹ * Q.polarBilin x.val a = 0
  have hx : Q.polarBilin x.val a = 0 := x.prop
  rw [hx, mul_zero]

include ha in
theorem lineRemainder_mem (x : V) : x - lineCoordinate Q a x • a ∈ linePerp Q a := by
  change Q.polarBilin (x-lineCoordinate Q a x • a) a = 0
  rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply]
  change Q.polarBilin x a - ((Q.polarBilin a a)⁻¹ * Q.polarBilin x a) * Q.polarBilin a a = 0
  field_simp
  ring

def lineSplit : V ≃ₗ[F] F × linePerp Q a where
  toFun x := (lineCoordinate Q a x, ⟨x-lineCoordinate Q a x • a, lineRemainder_mem Q a ha x⟩)
  invFun x := x.1 • a + x.2.val
  left_inv x := by change lineCoordinate Q a x • a + (x-lineCoordinate Q a x • a) = x; abel
  right_inv x := by
    apply Prod.ext
    · change lineCoordinate Q a (x.1 • a + x.2.val) = x.1
      rw [map_add, map_smul, lineCoordinate_self Q a ha, lineCoordinate_perp, smul_eq_mul, mul_one, add_zero]
    · apply Subtype.ext
      change x.1 • a + x.2.val - lineCoordinate Q a (x.1 • a+x.2.val) • a = x.2.val
      rw [map_add, map_smul, lineCoordinate_self Q a ha, lineCoordinate_perp, smul_eq_mul, mul_one, add_zero]
      abel
  map_add' x y := by
    apply Prod.ext
    · exact map_add _ _ _
    · apply Subtype.ext
      change x+y-lineCoordinate Q a (x+y) • a = (x-lineCoordinate Q a x • a)+(y-lineCoordinate Q a y • a)
      rw [map_add, _root_.add_smul]
      abel
  map_smul' c x := by
    apply Prod.ext
    · exact map_smul _ _ _
    · apply Subtype.ext
      change c • x-lineCoordinate Q a (c • x) • a = c • (x-lineCoordinate Q a x • a)
      rw [map_smul, smul_sub, smul_smul, smul_eq_mul]

include ha in
theorem linePerp_finrank [FiniteDimensional F V] : Module.finrank F (linePerp Q a) + 1 = Module.finrank F V := by
  have h := (lineSplit Q a ha).finrank_eq
  simpa only [Module.finrank_prod, Module.finrank_self, Nat.add_comm] using h.symm

def linePerpForm : QuadraticForm F (linePerp Q a) := Q.comp (linePerp Q a).subtype

@[simp] theorem linePerpForm_polar (x y : linePerp Q a) :
    (linePerpForm Q a).polarBilin x y = Q.polarBilin x.val y.val := by
  rw [linePerpForm, QuadraticMap.polarBilin_comp]
  rfl

include ha in
theorem lineSplit_form (x : F × linePerp Q a) :
    Q ((lineSplit Q a ha).symm x) = x.1^2 * Q a + Q x.2.val := by
  have hx : Q.polarBilin x.2.val a = 0 := x.2.prop
  have hax : Q.polarBilin a x.2.val = 0 := (polar_swap Q a x.2.val).trans hx
  change Q (x.1 • a + x.2.val) = _
  rw [QuadraticMap.map_add Q]
  change Q (x.1 • a) + Q x.2.val + Q.polarBilin (x.1 • a) x.2.val = _
  rw [Q.map_smul, map_smul, LinearMap.smul_apply, hax, smul_zero]
  simp only [smul_eq_mul, pow_two, add_zero]

include ha in
theorem linePerpForm_nondegenerate (hQ : Q.polarBilin.Nondegenerate) :
    (linePerpForm Q a).polarBilin.Nondegenerate := by
  have hl : ∀ x : linePerp Q a, (∀ y, (linePerpForm Q a).polarBilin x y = 0) → x = 0 := by
    intro x hx
    apply Subtype.ext
    apply hQ.1
    intro y
    let t := lineSplit Q a ha y
    have hy := (lineSplit Q a ha).symm_apply_apply y
    change t.1 • a + t.2.val = y at hy
    have hxa : Q.polarBilin x.val a = 0 := x.prop
    have hxt : Q.polarBilin x.val t.2.val = 0 := (linePerpForm_polar Q a x t.2).symm.trans (hx t.2)
    rw [← hy, map_add, map_smul, hxa, hxt, smul_zero, zero_add]
  constructor
  · exact hl
  · intro x hx
    apply hl x
    intro y
    rw [polar_swap]
    exact hx y

end ClassicalOrthogonal.Quadratic

namespace ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (a : V) (ha : Q.polarBilin a a ≠ 0)

def lineExtensionLinear (k : (linePerpForm Q a).IsometryEquiv (linePerpForm Q a)) : V ≃ₗ[F] V :=
  (lineSplit Q a ha).trans (((LinearEquiv.refl F F).prodCongr k.toLinearEquiv).trans
    (lineSplit Q a ha).symm)

theorem lineExtension_preserves (k : (linePerpForm Q a).IsometryEquiv (linePerpForm Q a)) (x : V) :
    Q (lineExtensionLinear Q a ha k x) = Q x := by
  change Q ((lineSplit Q a ha).symm ((lineSplit Q a ha x).1, k (lineSplit Q a ha x).2)) = Q x
  rw [lineSplit_form]
  have h := lineSplit_form Q a ha (lineSplit Q a ha x)
  rw [LinearEquiv.symm_apply_apply] at h
  rw [h]
  have hk := k.map_app (lineSplit Q a ha x).2
  exact congrArg (_ + ·) hk

def lineExtension (k : (linePerpForm Q a).IsometryEquiv (linePerpForm Q a)) : Q.IsometryEquiv Q where
  __ := lineExtensionLinear Q a ha k
  map_app' := lineExtension_preserves Q a ha k

include ha in
theorem lineSplit_self : lineSplit Q a ha a = (1, 0) := by
  apply Prod.ext
  · exact lineCoordinate_self Q a ha
  · apply Subtype.ext
    change a - lineCoordinate Q a a • a = 0
    rw [lineCoordinate_self Q a ha, one_smul, sub_self]

include ha in
theorem lineSplit_perp (x : linePerp Q a) : lineSplit Q a ha x.val = (0, x) := by
  apply Prod.ext
  · exact lineCoordinate_perp Q a x
  · apply Subtype.ext
    change x.val - lineCoordinate Q a x.val • a = x.val
    rw [lineCoordinate_perp, zero_smul, sub_zero]

theorem lineExtension_fix (k : (linePerpForm Q a).IsometryEquiv (linePerpForm Q a)) :
    lineExtension Q a ha k a = a := by
  change (lineSplit Q a ha).symm ((lineSplit Q a ha a).1, k (lineSplit Q a ha a).2) = a
  rw [lineSplit_self]
  simp only [map_zero]
  change (1 : F) • a + (0 : V) = a
  simp

theorem lineExtension_apply (k : (linePerpForm Q a).IsometryEquiv (linePerpForm Q a))
    (x : linePerp Q a) : lineExtension Q a ha k x.val = (k x).val := by
  change (lineSplit Q a ha).symm ((lineSplit Q a ha x.val).1, k (lineSplit Q a ha x.val).2) = (k x).val
  rw [lineSplit_perp]
  change (0 : F) • a + (k x).val = (k x).val
  simp

include ha in
theorem linear_ext_linePerp (g h : V →ₗ[F] V) (he : g a = h a)
    (hw : ∀ x : linePerp Q a, g x.val = h x.val) : g = h := by
  apply LinearMap.ext
  intro x
  have hx := (lineSplit Q a ha).symm_apply_apply x
  change (lineSplit Q a ha x).1 • a + (lineSplit Q a ha x).2.val = x at hx
  calc
    g x = g ((lineSplit Q a ha x).1 • a + (lineSplit Q a ha x).2.val) := congrArg g hx.symm
    _ = h ((lineSplit Q a ha x).1 • a + (lineSplit Q a ha x).2.val) := by rw [map_add, map_add, map_smul, map_smul, he, hw]
    _ = h x := congrArg h hx

def lineRestriction (g : Q.IsometryEquiv Q) (hg : g a = a) :
    (linePerpForm Q a).IsometryEquiv (linePerpForm Q a) where
  toFun x := ⟨g x.val, by
    change Q.polarBilin (g x.val) a = 0
    have h := isometry_polar Q g x.val a
    rw [hg] at h
    exact h.trans x.prop⟩
  invFun x := ⟨g.symm x.val, by
    change Q.polarBilin (g.symm x.val) a = 0
    have hga : g.symm a = a := by rw [← hg, g.symm_apply_apply]; exact hg.symm
    have h := isometry_polar Q g.symm x.val a
    rw [hga] at h
    exact h.trans x.prop⟩
  left_inv x := Subtype.ext (g.symm_apply_apply x.val)
  right_inv x := Subtype.ext (g.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add g x.val y.val)
  map_smul' c x := Subtype.ext (map_smul g c x.val)
  map_app' x := g.map_app x.val

theorem lineExtension_restriction (g : Q.IsometryEquiv Q) (hg : g a = a) :
    lineExtension Q a ha (lineRestriction Q a g hg) = g := by
  apply DFunLike.ext
  intro x
  have h := linear_ext_linePerp Q a ha
    (lineExtension Q a ha (lineRestriction Q a g hg)).toLinearEquiv.toLinearMap g.toLinearEquiv.toLinearMap
    ((lineExtension_fix Q a ha _).trans hg.symm)
    (fun w => lineExtension_apply Q a ha _ w)
  exact LinearMap.congr_fun h x


/-- A reflection in the perpendicular space extends to that same ambient reflection. -/
theorem lineExtension_reflection (u : linePerp Q a) (hu : Q u.val ≠ 0) :
    lineExtension Q a ha (reflectionIsometry (linePerpForm Q a) u hu) =
      reflectionIsometry Q u.val hu := by
  have hfix : reflectionIsometry Q u.val hu a = a := by
    change reflectionLinear Q u.val hu a = a
    rw [reflectionLinear_apply, polar_swap Q a u.val]
    have hp : Q.polarBilin u.val a = 0 := u.prop
    rw [hp, mul_zero, zero_smul, sub_zero]
  have hp : ∀ w : linePerp Q a,
      lineExtension Q a ha (reflectionIsometry (linePerpForm Q a) u hu) w.val =
        reflectionIsometry Q u.val hu w.val := by
    intro w
    rw [lineExtension_apply]
    change ((reflectionLinear (linePerpForm Q a) u hu w) : linePerp Q a).val =
      reflectionLinear Q u.val hu w.val
    rw [reflectionLinear_apply (linePerpForm Q a) u hu w, reflectionLinear_apply Q u.val hu w.val]
    change w.val - (((linePerpForm Q a) u)⁻¹ * (linePerpForm Q a).polarBilin w u) • u.val = _
    rw [linePerpForm_polar]
    rfl
  apply DFunLike.ext
  intro x
  exact LinearMap.congr_fun (linear_ext_linePerp Q a ha _ _
    ((lineExtension_fix Q a ha _).trans hfix.symm) hp) x

end ClassicalOrthogonal.Quadratic

namespace ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

theorem reflection_equal_value (u v : V) (hval : Q u = Q v) (huv : Q (u-v) ≠ 0) :
    reflectionLinear Q (u-v) huv u = v := by
  have hp : Q.polarBilin u (u-v) = Q (u-v) := by
    rw [map_sub, polar_self, sub_value, hval]
    ring
  rw [reflectionLinear_apply, hp, inv_mul_cancel₀ huv, one_smul, sub_sub_cancel]

@[simp] theorem reflection_self (a : V) (ha : Q a ≠ 0) : reflectionLinear Q a ha a = -a :=
  Module.reflection_apply_self _


end ClassicalOrthogonal.Quadratic

namespace ClassicalOrthogonal.ReflectionGeneration
open ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

theorem reflectionSubgroup_transport (h2 : (2 : F) ≠ 0) (u v : V)
    (hu : Q u ≠ 0) (hval : Q u = Q v) :
    ∃ g : quadraticIsometrySubgroup Q, g ∈ reflectionSubgroup Q ∧ g.val u = v := by
  by_cases hsub : Q (u-v) = 0
  · have hsum : Q (u+v) ≠ 0 := by
      have hs := sub_value Q u v
      have ha := QuadraticMap.map_add Q u v
      change Q (u+v) = Q u + Q v + Q.polarBilin u v at ha
      have he : Q (u+v) = (2 : F)^2 * Q u := by rw [hval] at hs ha ⊢; linear_combination ha + hs - hsub
      rw [he]
      exact mul_ne_zero (pow_ne_zero _ h2) hu
    have hd : Q (u-(-v)) ≠ 0 := by simpa only [sub_neg_eq_add] using hsum
    let r := reflectionElement Q (u-(-v)) hd
    let s := reflectionElement Q v (hval ▸ hu)
    refine ⟨s*r, (reflectionSubgroup Q).mul_mem (reflectionElement_mem _ _ _) (reflectionElement_mem _ _ _), ?_⟩
    change s.val (r.val u) = v
    have hr : r.val u = -v := reflection_equal_value Q u (-v) (by rwa [Q.map_neg]) hd
    rw [hr, map_neg]
    change -(reflectionLinear Q v (hval ▸ hu) v) = v
    rw [reflection_self, neg_neg]
  · exact ⟨reflectionElement Q (u-v) hsub, reflectionElement_mem _ _ _, reflection_equal_value Q u v hval hsub⟩

variable (a : V) (ha : Q.polarBilin a a ≠ 0)

def lineExtensionHom : quadraticIsometrySubgroup (linePerpForm Q a) →* quadraticIsometrySubgroup Q where
  toFun g := (isometryCarrierEquiv Q).symm (lineExtension Q a ha (isometryCarrierEquiv _ g))
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact LinearMap.congr_fun (linear_ext_linePerp Q a ha _ _
      (lineExtension_fix Q a ha _) (fun w => lineExtension_apply Q a ha _ w)) x
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply LinearMap.congr_fun (linear_ext_linePerp Q a ha _ _ ?_ ?_) x
    · change lineExtension Q a ha (isometryCarrierEquiv _ (g*h)) a =
        lineExtension Q a ha (isometryCarrierEquiv _ g) (lineExtension Q a ha (isometryCarrierEquiv _ h) a)
      rw [lineExtension_fix, lineExtension_fix, lineExtension_fix]
    · intro w
      change lineExtension Q a ha (isometryCarrierEquiv _ (g*h)) w.val =
        lineExtension Q a ha (isometryCarrierEquiv _ g) (lineExtension Q a ha (isometryCarrierEquiv _ h) w.val)
      rw [lineExtension_apply, lineExtension_apply, lineExtension_apply]
      rfl

theorem lineExtensionHom_reflection (u : linePerp Q a) (hu : (linePerpForm Q a) u ≠ 0) :
    lineExtensionHom Q a ha (reflectionElement (linePerpForm Q a) u hu) = reflectionElement Q u.val hu := by
  change (isometryCarrierEquiv Q).symm (lineExtension Q a ha (reflectionIsometry (linePerpForm Q a) u hu)) = _
  rw [lineExtension_reflection Q a ha u hu]
  rfl

theorem lineExtensionHom_mem (k : quadraticIsometrySubgroup (linePerpForm Q a))
    (hk : k ∈ reflectionSubgroup (linePerpForm Q a)) :
    lineExtensionHom Q a ha k ∈ reflectionSubgroup Q := by
  have hl : reflectionSubgroup (linePerpForm Q a) ≤ (reflectionSubgroup Q).comap (lineExtensionHom Q a ha) := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨u, hu, rfl⟩
    change lineExtensionHom Q a ha (reflectionElement (linePerpForm Q a) u hu) ∈ reflectionSubgroup Q
    rw [lineExtensionHom_reflection]
    exact reflectionElement_mem Q u.val hu
  exact hl hk

end ClassicalOrthogonal.ReflectionGeneration

namespace ClassicalOrthogonal.ReflectionGeneration
open ClassicalOrthogonal.Quadratic

/-- Dimension induction uses actual nondegenerate-line restriction and reflection extension. -/
theorem reflection_generation_dim (F : Type u) [Field F] (h2 : (2 : F) ≠ 0) (d : ℕ) :
    ∀ (W : Type u) [AddCommGroup W] [Module F W] [FiniteDimensional F W],
      Module.finrank F W = d → ∀ (Q : QuadraticForm F W), Q.polarBilin.Nondegenerate →
        reflectionSubgroup Q = ⊤ := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro W _ _ _ hd Q hQ
    by_cases hz : d = 0
    · have : Subsingleton W := Module.finrank_zero_iff.mp (hd.trans hz)
      apply top_unique
      intro g _
      have hg : g = 1 := Subtype.ext (Subsingleton.elim _ _)
      rw [hg]
      exact (reflectionSubgroup Q).one_mem
    · have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := F) (M := W) (by omega)
      obtain ⟨x, hx⟩ := exists_ne (0 : W)
      have hex : ∃ a : W, Q a ≠ 0 := by
        by_contra! hzero
        apply hx
        apply hQ.1
        intro y
        simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hzero, sub_zero]
      obtain ⟨a, hqa⟩ := hex
      have haa : Q.polarBilin a a ≠ 0 := by rw [polar_self]; exact mul_ne_zero h2 hqa
      have hdim := linePerp_finrank Q a haa
      have hlt : Module.finrank F (linePerp Q a) < d := by omega
      have hgen := ih (Module.finrank F (linePerp Q a)) hlt (linePerp Q a) rfl
        (linePerpForm Q a) (linePerpForm_nondegenerate Q a haa hQ)
      apply top_unique
      intro g _
      have hga : Q (g.val a) ≠ 0 := by rw [isometry_preserves]; exact hqa
      obtain ⟨r, hr, hrg⟩ := reflectionSubgroup_transport Q h2 (g.val a) a hga (isometry_preserves Q g a)
      let k := r*g
      have hkfix : (isometryCarrierEquiv Q k) a = a := hrg
      let kc := (isometryCarrierEquiv (linePerpForm Q a)).symm
        (lineRestriction Q a (isometryCarrierEquiv Q k) hkfix)
      have hkc : kc ∈ reflectionSubgroup (linePerpForm Q a) := by rw [hgen]; trivial
      have he : lineExtensionHom Q a haa kc = k := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro y
        exact congrArg (fun t : Q.IsometryEquiv Q => t y)
          (lineExtension_restriction Q a haa (isometryCarrierEquiv Q k) hkfix)
      have hk := lineExtensionHom_mem Q a haa kc hkc
      rw [he] at hk
      have hg := (reflectionSubgroup Q).mul_mem ((reflectionSubgroup Q).inv_mem hr) hk
      change r⁻¹ * (r*g) ∈ reflectionSubgroup Q at hg
      simpa only [inv_mul_cancel_left] using hg

/-- Cartan–Dieudonné generation for the actual full quadratic-isometry carrier. -/
theorem reflectionSubgroup_eq_top {F : Type u} [Field F] {V : Type u}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0) :
    reflectionSubgroup Q = ⊤ :=
  reflection_generation_dim F h2 (Module.finrank F V) V rfl Q hQ

end ClassicalOrthogonal.ReflectionGeneration
