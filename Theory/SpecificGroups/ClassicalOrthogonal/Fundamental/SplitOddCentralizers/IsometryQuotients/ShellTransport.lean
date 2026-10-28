/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.IsometryQuotients.ReflectionGeneration
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.JointGeneration
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Elementary transport of equal nonzero quadratic values

Two orthogonal hyperbolic pairs supply a hyperbolic plane in every polar
hyperplane. Singular vectors span a space with a hyperbolic plane, so a
nonzero restricted polar functional has a singular witness. An explicit
Siegel transformation then transports vectors of equal nonzero value;
opposite vectors are joined through a third vector.

Adapted from `Atlas/LinearAlgebra/QuadraticPerpHyperbolic.lean`,
`QuadraticWittTwo.lean`, `QuadraticSingularSpan.lean`,
`QuadraticSingularPerpendicular.lean`, `QuadraticSiegelTransport.lean`, and
`Atlas/LinearGroups/Orthogonal/ElementaryTransitivity.lean`.
We reuse CFSG's actual forms, complement splitting and reflection transport,
and adapt namespaces and public boundaries for Lean 4.33.
Source: GLS3 §2.7, elementary orthogonal transformations.
-/

@[expose] public noncomputable section
universe u
open Theory.AlgebraicGroup

namespace ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- An isotropic plane meets any polar hyperplane in a nonzero singular vector. -/
theorem isotropic_plane_perpendicular (e₁ e₂ d : V)
    (he₁ : Q e₁ = 0) (he₂ : Q e₂ = 0) (he₁₂ : Q.polarBilin e₁ e₂ = 0)
    (hne : e₁ ≠ 0) (hind : ∀ c : F, e₂ ≠ c • e₁) :
    ∃ a, a ≠ 0 ∧ Q a = 0 ∧ Q.polarBilin a d = 0 := by
  by_cases h : Q.polarBilin e₁ d = 0
  · exact ⟨e₁, hne, he₁, h⟩
  · let c := Q.polarBilin e₂ d / Q.polarBilin e₁ d
    refine ⟨e₂-c • e₁, ?_, ?_, ?_⟩
    · exact sub_ne_zero.mpr (hind c)
    · rw [sub_eq_add_neg, ← neg_smul, add_smul, he₁, he₂, polar_swap Q e₂ e₁, he₁₂]
      ring
    · rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact sub_eq_zero.mpr (div_mul_cancel₀ _ h).symm

/-- A singular vector perpendicular to a nonsingular line has a hyperbolic partner there. -/
theorem perpendicular_hyperbolic_partner (hQ : Q.polarBilin.Nondegenerate)
    (d a : V) (hd : Q.polarBilin d d ≠ 0) (ha : Q a = 0)
    (hne : a ≠ 0) (had : Q.polarBilin a d = 0) :
    ∃ b, Q b = 0 ∧ Q.polarBilin a b = 1 ∧ Q.polarBilin b d = 0 := by
  obtain ⟨b₀, hb₀⟩ := exists_normalized_partner Q a (fun h => hne (hQ.1 a h))
  let b₁ := b₀ - (Q.polarBilin b₀ d / Q.polarBilin d d) • d
  have hab : Q.polarBilin a b₁ = 1 := by
    dsimp [b₁]
    rw [map_sub, map_smul, had, smul_zero, sub_zero, hb₀]
  have hbd : Q.polarBilin b₁ d = 0 := by
    dsimp [b₁]
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      div_mul_cancel₀ _ hd, sub_self]
  refine ⟨b₁ - Q b₁ • a, (partner_correction Q a b₁ ha hab).1,
    (partner_correction Q a b₁ ha hab).2, ?_⟩
  rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, had, smul_zero, sub_zero, hbd]

end ClassicalOrthogonal.Quadratic

namespace ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]

/-- Two perpendicular hyperbolic pairs in the actual quadratic space. -/
structure WittTwoFrame (Q : QuadraticForm F V) where
  e₁ : V
  f₁ : V
  e₂ : V
  f₂ : V
  qe₁ : Q e₁ = 0
  qf₁ : Q f₁ = 0
  qe₂ : Q e₂ = 0
  qf₂ : Q f₂ = 0
  pair₁ : Q.polarBilin e₁ f₁ = 1
  pair₂ : Q.polarBilin e₂ f₂ = 1
  ee : Q.polarBilin e₂ e₁ = 0
  ef : Q.polarBilin e₂ f₁ = 0
  fe : Q.polarBilin f₂ e₁ = 0
  ff : Q.polarBilin f₂ f₁ = 0

variable (Q : QuadraticForm F V) (H : WittTwoFrame Q)

theorem WittTwoFrame.first_ne_zero : H.e₁ ≠ 0 := by
  intro h
  have hp := H.pair₁
  rw [h, map_zero, LinearMap.zero_apply] at hp
  exact zero_ne_one hp

theorem WittTwoFrame.second_not_multiple (c : F) : H.e₂ ≠ c • H.e₁ := by
  intro h
  have hc := H.ef
  rw [h, map_smul, LinearMap.smul_apply, smul_eq_mul, H.pair₁, mul_one] at hc
  have hp := H.pair₂
  rw [h, hc, zero_smul, map_zero, LinearMap.zero_apply] at hp
  exact zero_ne_one hp

include H in
/-- Every polar hyperplane contains a hyperbolic plane in odd characteristic and Witt index ≥2. -/
theorem hyperbolic_pair_in_perpendicular (hQ : Q.polarBilin.Nondegenerate)
    (h2 : (2 : F) ≠ 0) (d : V) :
    ∃ a b, Q a = 0 ∧ Q b = 0 ∧ Q.polarBilin a b = 1 ∧
      Q.polarBilin a d = 0 ∧ Q.polarBilin b d = 0 := by
  by_cases hd0 : d = 0
  · subst d
    exact ⟨H.e₁, H.f₁, H.qe₁, H.qf₁, H.pair₁, by simp, by simp⟩
  by_cases hqd : Q d = 0
  · have hrad : Q.radical = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      exact (Submodule.mem_bot F).mpr (hQ.1 x (fun y => LinearMap.congr_fun hx.2 y))
    obtain ⟨g₀, _, hg₀⟩ := ReflectionGeneration.reflectionSubgroup_singular_transport Q hrad d H.e₁ hd0
      (WittTwoFrame.first_ne_zero Q H) hqd H.qe₁
    let g := ReflectionGeneration.isometryCarrierEquiv Q g₀
    have hg : g d = H.e₁ := hg₀
    refine ⟨g.symm H.e₂, g.symm H.f₂, (g.symm.map_app _).trans H.qe₂,
      (g.symm.map_app _).trans H.qf₂, ?_, ?_, ?_⟩
    · exact (isometry_polar Q g.symm _ _).trans H.pair₂
    · have h := isometry_polar Q g (g.symm H.e₂) d
      rw [g.apply_symm_apply, hg] at h
      exact h.symm.trans H.ee
    · have h := isometry_polar Q g (g.symm H.f₂) d
      rw [g.apply_symm_apply, hg] at h
      exact h.symm.trans H.fe
  · obtain ⟨a, hane, ha, had⟩ := isotropic_plane_perpendicular Q H.e₁ H.e₂ d
      H.qe₁ H.qe₂ ((polar_swap Q _ _).trans H.ee)
      (WittTwoFrame.first_ne_zero Q H) (WittTwoFrame.second_not_multiple Q H)
    have hdd : Q.polarBilin d d ≠ 0 := by rw [polar_self]; exact mul_ne_zero h2 hqd
    obtain ⟨b, hb, hab, hbd⟩ := perpendicular_hyperbolic_partner Q hQ d a hdd ha hane had
    exact ⟨a, b, ha, hb, hab, had, hbd⟩

end ClassicalOrthogonal.Quadratic

namespace ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (e f : V)
  (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)

include he hf hef in
/-- A perpendicular vector is the sum of three singular vectors. -/
theorem complement_singular_decomposition (w : complement Q e f) :
    Q (w.val + e - Q w.val • f) = 0 := by
  have hwe : Q.polarBilin w.val e = 0 := w.prop.1
  have hwf : Q.polarBilin w.val f = 0 := w.prop.2
  have hqe : Q (w.val + e) = Q w.val := by
    rw [QuadraticMap.map_add Q]
    change Q w.val + Q e + Q.polarBilin w.val e = Q w.val
    rw [he, hwe, add_zero, add_zero]
  rw [sub_eq_add_neg, ← neg_smul, add_smul, hqe]
  simp only [hf, map_add, LinearMap.add_apply, hwf, hef, mul_zero, add_zero]
  ring

include e f he hf hef in
/-- A linear functional vanishing on singular vectors vanishes everywhere. -/
theorem linear_zero_of_singular (l : V →ₗ[F] F)
    (hl : ∀ x, Q x = 0 → l x = 0) : l = 0 := by
  have hlw : ∀ w : complement Q e f, l w.val = 0 := by
    intro w
    have h := hl _ (complement_singular_decomposition Q e f he hf hef w)
    rw [map_sub, map_add, map_smul, hl e he, hl f hf, smul_zero, add_zero, sub_zero] at h
    exact h
  apply LinearMap.ext
  intro x
  let t := split Q e f he hf hef x
  have hx : x = t.1.1 • e + t.1.2 • f + t.2.val :=
    ((split Q e f he hf hef).symm_apply_apply x).symm
  rw [hx, map_add, map_add, map_smul, map_smul, hl e he, hl f hf, hlw,
    smul_zero, smul_zero, zero_add, add_zero]
  rfl

include e f he hf hef in
/-- A nonzero linear functional has a singular witness. -/
theorem exists_singular_functional_ne_zero (l : V →ₗ[F] F) (hl : l ≠ 0) :
    ∃ x, Q x = 0 ∧ l x ≠ 0 := by
  classical
  by_contra! h
  exact hl (linear_zero_of_singular Q e f he hf hef l h)

end ClassicalOrthogonal.Quadratic

namespace ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)

include hQ in
theorem polar_restriction_ne_zero (u d : V) (hu : u ∉ Submodule.span F {d}) :
    (Q.polarBilin u).comp (linePerp Q d).subtype ≠ 0 := by
  intro h
  apply hu
  have hr : Q.polarBilin.IsRefl := fun x y h => (polar_swap Q y x).trans h
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hQ hr (Submodule.span F {d})]
  intro x hx
  have hdx := hx d (Submodule.subset_span (Set.mem_singleton d))
  have hxd : Q.polarBilin x d = 0 := (polar_swap Q x d).trans hdx
  have hp := LinearMap.congr_fun h (⟨x, hxd⟩ : linePerp Q d)
  exact (polar_swap Q x u).trans hp

include hQ in
/-- Away from the perpendicular line itself, a polar functional has a singular witness. -/
theorem exists_singular_perpendicular_witness (H : WittTwoFrame Q) (h2 : (2 : F) ≠ 0)
    (u d : V) (hu : u ∉ Submodule.span F {d}) :
    ∃ w, Q w = 0 ∧ Q.polarBilin w d = 0 ∧ Q.polarBilin u w ≠ 0 := by
  obtain ⟨a, b, ha, hb, hab, had, hbd⟩ := hyperbolic_pair_in_perpendicular Q H hQ h2 d
  let a' : linePerp Q d := ⟨a, had⟩
  let b' : linePerp Q d := ⟨b, hbd⟩
  have hp : (linePerpForm Q d).polarBilin a' b' = 1 := by
    rw [linePerpForm_polar]
    exact hab
  obtain ⟨w, hw, hlw⟩ := exists_singular_functional_ne_zero (linePerpForm Q d) a' b'
    ha hb hp ((Q.polarBilin u).comp (linePerp Q d).subtype)
    (polar_restriction_ne_zero Q hQ u d hu)
  exact ⟨w.val, hw, w.prop, hlw⟩

end ClassicalOrthogonal.Quadratic

namespace ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (u v w : V)
  (hw : Q w = 0) (hval : Q u = Q v)
  (hp : Q.polarBilin u w = Q.polarBilin v w) (hne : Q.polarBilin u w ≠ 0)

def transportParameter : V := (Q.polarBilin u w)⁻¹ • (u-v)

include hp in
theorem transportParameter_perp : Q.polarBilin w (transportParameter Q u v w) = 0 := by
  have h : Q.polarBilin w u = Q.polarBilin w v := by
    rw [polar_swap Q w u, polar_swap Q w v]
    exact hp
  rw [transportParameter, map_smul, map_sub, h, sub_self, smul_zero]

include hval in
theorem difference_polar_value : Q.polarBilin u (u-v) = Q (u-v) := by
  rw [map_sub, polar_self, sub_eq_add_neg u v, ← neg_one_smul F v, add_smul]
  rw [hval]
  ring

include hval hne in
/-- Equal quadratic values and equal nonzero pairing with a singular direction suffice. -/
theorem siegel_equal_value_transport : siegel Q w (transportParameter Q u v w) u = v := by
  have hdiff := difference_polar_value Q u v hval
  simp only [siegel, transportParameter, map_smul, smul_eq_mul, Q.map_smul, smul_smul]
  rw [hdiff]
  match_scalars <;> field_simp <;> ring

end ClassicalOrthogonal.Quadratic

namespace ClassicalOrthogonal.ReflectionGeneration
open ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- One actual elementary transformation gives equal-value transport along a singular direction. -/
theorem elementary_transport_with_direction (u v w : V) (hw : Q w = 0)
    (hval : Q u = Q v) (hp : Q.polarBilin u w = Q.polarBilin v w)
    (hne : Q.polarBilin u w ≠ 0) :
    ∃ g : quadraticIsometrySubgroup Q, g ∈ elementarySubgroup Q ∧ g.val u = v := by
  let t := transportParameter Q u v w
  have ht := transportParameter_perp Q u v w hp
  exact ⟨siegelElement Q w t hw ht, siegelElement_mem Q w t hw ht,
    siegel_equal_value_transport Q u v w hval hne⟩

/-- Equal nonzero quadratic values can be collinear with their difference only at opposites. -/
theorem nonsingular_not_span_difference (u v : V) (hu : Q u ≠ 0)
    (hval : Q u = Q v) (hopp : v ≠ -u) : u ∉ Submodule.span F {u-v} := by
  rintro h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  have hcu : u = c • (u-v) := hc.symm
  have hd : Q (u-v) ≠ 0 := by
    intro hd
    apply hu
    rw [hcu, Q.map_smul, hd, smul_zero]
  have hp := congrArg (fun x : V => Q.polarBilin x (u-v)) hc
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, polar_self,
    difference_polar_value Q u v hval] at hp
  have hc2 : (2 : F) * c = 1 := by
    apply (mul_right_cancel₀ hd)
    linear_combination hp
  have he : u+u = u-v := by
    have ht := congrArg (fun z : V => (2 : F) • z) hcu
    rw [smul_smul, hc2, one_smul] at ht
    simpa only [two_smul] using ht
  apply hopp
  apply eq_neg_iff_add_eq_zero.mpr
  have ht := congrArg (fun z : V => z+v-u) he
  convert ht using 1 <;> abel

variable [FiniteDimensional F V] (H : WittTwoFrame Q)
  (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)

include H hQ h2 in
/-- Apart from opposite vectors, one Siegel transformation suffices in Witt index at least two. -/
theorem elementary_transport_not_opposite (u v : V) (hu : Q u ≠ 0)
    (hval : Q u = Q v) (hopp : v ≠ -u) :
    ∃ g : quadraticIsometrySubgroup Q, g ∈ elementarySubgroup Q ∧ g.val u = v := by
  obtain ⟨w, hw, hwd, huw⟩ := exists_singular_perpendicular_witness Q hQ H h2 u (u-v)
    (nonsingular_not_span_difference Q u v hu hval hopp)
  have hp : Q.polarBilin u w = Q.polarBilin v w := by
    rw [map_sub] at hwd
    have hp := sub_eq_zero.mp hwd
    simpa only [polar_swap Q w u, polar_swap Q w v] using hp
  exact elementary_transport_with_direction Q u v w hw hval hp huw

include H hQ h2 in
/-- The actual elementary group is transitive on each nonzero quadratic-value shell. -/
theorem elementary_transport_equal_value (u v : V) (hu : Q u ≠ 0)
    (hval : Q u = Q v) :
    ∃ g : quadraticIsometrySubgroup Q, g ∈ elementarySubgroup Q ∧ g.val u = v := by
  by_cases hopp : v = -u
  · subst v
    obtain ⟨a, b, ha, hb, hab, hau, hbu⟩ := hyperbolic_pair_in_perpendicular Q H hQ h2 u
    have hane : a ≠ 0 := by
      intro h
      rw [h, map_zero, LinearMap.zero_apply] at hab
      exact zero_ne_one hab
    have hua : Q.polarBilin u a = 0 := (polar_swap Q u a).trans hau
    have hza : Q (u+a) = Q u := by
      rw [QuadraticMap.map_add Q]
      change Q u + Q a + Q.polarBilin u a = Q u
      rw [ha, hua, add_zero, add_zero]
    have hzn : u+a ≠ -u := by
      intro h
      have he : a = (-2 : F) • u := by
        have ht := congrArg (fun z : V => z-u) h
        convert ht using 1 <;> module
      rw [he, Q.map_smul, smul_eq_mul] at ha
      exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) (neg_ne_zero.mpr h2)) hu ha
    have hzn' : -u ≠ -(u+a) := by
      intro h
      have ht := neg_injective h.symm
      apply hane
      exact add_left_cancel (ht.trans (add_zero u).symm)
    obtain ⟨g, hg, hgu⟩ := elementary_transport_not_opposite Q H hQ h2 u (u+a) hu hza.symm hzn
    obtain ⟨k, hk, hka⟩ := elementary_transport_not_opposite Q H hQ h2 (u+a) (-u)
      (hza ▸ hu) (hza.trans (Q.map_neg u).symm) hzn'
    refine ⟨k*g, (elementarySubgroup Q).mul_mem hk hg, ?_⟩
    change k.val (g.val u) = -u
    rw [hgu, hka]
  · exact elementary_transport_not_opposite Q H hQ h2 u v hu hval hopp

end ClassicalOrthogonal.ReflectionGeneration

