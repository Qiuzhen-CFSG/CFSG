/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.PairStabilizer
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.StandardComplement

/-!
# Joint generation by elementary transformations and reflections

Adapted from `Atlas/LinearGroups/Orthogonal/ElementaryReflectionGeneration.lean`
and `Atlas/LinearAlgebra/QuadraticPairTransport.lean`. Reflection transport
moves the first vector of a hyperbolic pair, then one explicit Siegel
transformation corrects its partner. The remaining isometry restricts to the
smaller split complement, whose generators extend to the ambient space.
This proves joint generation in every rank, without incorrectly assuming
reflection generation in dimension four. We replace the source's root-group
and semilinear transport imports by the needed explicit formulas. Namespaces,
public boundaries and imports are adapted for CFSG / Lean 4.33.
-/

@[expose] public noncomputable section
universe u
open Theory.AlgebraicGroup

namespace ClassicalOrthogonal.ReflectionGeneration
open ClassicalOrthogonal.Quadratic
variable {F V W : Type u} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
variable (Q : QuadraticForm F V)

/-- The Siegel subgroup fixing e transports its singular normalized partners. -/
private theorem elementary_fixing_first (e f v : V) (he : Q e=0) (hf : Q f=0)
    (hv : Q v=0) (hef : Q.polarBilin e f=1) (hev : Q.polarBilin e v=1) :
    ∃ k : quadraticIsometrySubgroup Q, k ∈ elementarySubgroup Q ∧ k.val e=e ∧ k.val f=v := by
  let s := split Q e f he hf hef
  let w := (s v).2
  have hw := (mem_complement Q e f w.val).mp w.prop
  have hew : Q.polarBilin e w.val=0 := (polar_swap Q e w.val).trans hw.1
  have hfw : Q.polarBilin f w.val=0 := (polar_swap Q f w.val).trans hw.2
  have hve : Q.polarBilin v e=1 := (polar_swap Q v e).trans hev
  have hfe : Q.polarBilin f e=1 := (polar_swap Q f e).trans hef
  have ha : Q.polarBilin v f = -Q w.val := by
    have h := form_split Q e f he hf hef v
    change Q v=Q.polarBilin v f * Q.polarBilin v e+Q w.val at h
    rw [hv,hve,mul_one] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hn : Q.polarBilin e (-w.val)=0 := by rw [map_neg,hew,neg_zero]
  refine ⟨siegelElement Q e (-w.val) he hn, siegelElement_mem Q e (-w.val) he hn,
    siegel_fix Q e (-w.val) he hn,?_⟩
  have hd := s.symm_apply_apply v
  change Q.polarBilin v f • e+Q.polarBilin v e • f+w.val=v at hd
  rw [ha,hve,one_smul] at hd
  change siegel Q e (-w.val) f=v
  rw [← hd]
  simp only [siegel,map_neg,hfw,hfe,Q.map_neg,neg_zero,zero_smul,one_smul,mul_one]
  module

abbrev elementaryReflectionSubgroup : Subgroup (quadraticIsometrySubgroup Q) :=
  elementarySubgroup Q ⊔ reflectionSubgroup Q

private theorem elementary_mem_joint {g : quadraticIsometrySubgroup Q}
    (hg : g ∈ elementarySubgroup Q) : g ∈ elementaryReflectionSubgroup Q :=
  (show elementarySubgroup Q ≤ elementaryReflectionSubgroup Q from le_sup_left) hg

private theorem reflection_mem_joint {g : quadraticIsometrySubgroup Q}
    (hg : g ∈ reflectionSubgroup Q) : g ∈ elementaryReflectionSubgroup Q :=
  (show reflectionSubgroup Q ≤ elementaryReflectionSubgroup Q from le_sup_right) hg

private theorem reflection_transport_singular_nonperp (u v : V)
    (hu : Q u = 0) (hv : Q v = 0) (huv : Q.polarBilin u v ≠ 0) :
    ∃ g : quadraticIsometrySubgroup Q, g ∈ reflectionSubgroup Q ∧ g.val u = v := by
  have hq := sub_singular_value Q u v hu hv
  have ha : Q (u-v) ≠ 0 := by rw [hq]; exact neg_ne_zero.mpr huv
  refine ⟨reflectionElement Q (u-v) ha, reflectionElement_mem Q _ _, ?_⟩
  change reflectionLinear Q (u-v) ha u = v
  have hp : Q.polarBilin u (u-v) = -Q.polarBilin u v := by
    rw [map_sub, polar_self, hu, mul_zero, zero_sub]
  rw [reflectionLinear_apply, hp, hq, inv_mul_cancel₀ (neg_ne_zero.mpr huv), one_smul]
  abel

/-- The reflection subgroup itself transports nonzero singular vectors in all characteristics. -/
theorem reflectionSubgroup_singular_transport (hrad : Q.radical = ⊥) (u v : V)
    (hu : u ≠ 0) (hv : v ≠ 0) (hqu : Q u = 0) (hqv : Q v = 0) :
    ∃ g : quadraticIsometrySubgroup Q, g ∈ reflectionSubgroup Q ∧ g.val u = v := by
  by_cases huv : Q.polarBilin u v = 0
  · obtain ⟨w,hqw,huw,hvw⟩ := exists_singular_connector Q u v hqu huv
      (singular_not_polar_radical Q hrad u hu hqu)
      (singular_not_polar_radical Q hrad v hv hqv)
    obtain ⟨g,hg,hgu⟩ := reflection_transport_singular_nonperp Q u w hqu hqw huw
    obtain ⟨k,hk,hkw⟩ := reflection_transport_singular_nonperp Q w v hqw hqv
      (by rwa [polar_swap])
    exact ⟨k*g,(reflectionSubgroup Q).mul_mem hk hg,by change k.val (g.val u) = v; rw [hgu,hkw]⟩
  · exact reflection_transport_singular_nonperp Q u v hqu hqv huv

/-- Reflection transport followed by a root correction gives actual pair transitivity,
without a Witt-index lower bound. -/
theorem elementaryReflection_pair_transport (hrad : Q.radical = ⊥) (e f u v : V)
    (he : Q e = 0) (hf : Q f = 0) (hu : Q u = 0) (hv : Q v = 0)
    (hef : Q.polarBilin e f = 1) (huv : Q.polarBilin u v = 1) :
    ∃ g : quadraticIsometrySubgroup Q, g ∈ elementaryReflectionSubgroup Q ∧
      g.val e = u ∧ g.val f = v := by
  have hene : e ≠ 0 := by
    intro hz
    rw [hz,map_zero,LinearMap.zero_apply] at hef
    exact zero_ne_one hef
  have hune : u ≠ 0 := by
    intro hz
    rw [hz,map_zero,LinearMap.zero_apply] at huv
    exact zero_ne_one huv
  obtain ⟨g,hg,hge⟩ := reflectionSubgroup_singular_transport Q hrad e u hene hune he hu
  have hgf : Q (g.val f) = 0 := (isometry_preserves Q g f).trans hf
  have hpair : Q.polarBilin u (g.val f) = 1 := by
    have hp := isometry_polar Q (isometryCarrierEquiv Q g) e f
    change Q.polarBilin (g.val e) (g.val f) = Q.polarBilin e f at hp
    rw [hge,hef] at hp
    exact hp
  obtain ⟨r,hr,hru,hrf⟩ := elementary_fixing_first Q u (g.val f) v hu hgf hv hpair huv
  refine ⟨r*g,(elementaryReflectionSubgroup Q).mul_mem
    (elementary_mem_joint Q hr) (reflection_mem_joint Q hg), ?_, ?_⟩
  · change r.val (g.val e) = u
    rw [hge, hru]
  · exact hrf

variable (e f : V) (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)

/-- Extend an actual complement reflection to the same ambient reflecting vector. -/
theorem complementLift_reflection (u : complement Q e f)
    (hu : (complementForm Q e f) u ≠ 0) :
    complementLift Q e f he hf hef (reflectionElement (complementForm Q e f) u hu) =
      reflectionElement Q u.val hu := by
  let s := reflectionElement Q u.val hu
  have hse : s.val e = e := by
    change reflectionLinear Q u.val hu e = e
    rw [reflectionLinear_apply Q u.val hu e, (polar_swap Q e u.val).trans u.prop.1,
      mul_zero, zero_smul, sub_zero]
  have hsf : s.val f = f := by
    change reflectionLinear Q u.val hu f = f
    rw [reflectionLinear_apply Q u.val hu f, (polar_swap Q f u.val).trans u.prop.2,
      mul_zero, zero_smul, sub_zero]
  let t : pairStabilizer Q e f := ⟨s,hse,hsf⟩
  have ht : pairRestriction Q e f t = reflectionElement (complementForm Q e f) u hu := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change reflectionLinear Q u.val hu x.val =
      (reflectionLinear (complementForm Q e f) u hu x).val
    simp only [reflectionLinear_apply,complementForm_polar]
    rfl
  have hi : (pairStabilizerEquiv Q e f he hf hef).symm
      (reflectionElement (complementForm Q e f) u hu) = t := by
    apply (pairStabilizerEquiv Q e f he hf hef).injective
    exact ((pairStabilizerEquiv Q e f he hf hef).apply_symm_apply _).trans ht.symm
  exact congrArg Subtype.val hi

/-- The full joint subgroup in a complement extends into the ambient joint subgroup. -/
theorem complementLift_mem_elementaryReflection
    (g : quadraticIsometrySubgroup (complementForm Q e f))
    (hg : g ∈ elementaryReflectionSubgroup (complementForm Q e f)) :
    complementLift Q e f he hf hef g ∈ elementaryReflectionSubgroup Q := by
  have hle : elementaryReflectionSubgroup (complementForm Q e f) ≤
      (elementaryReflectionSubgroup Q).comap (complementLift Q e f he hf hef) := by
    apply sup_le
    · intro k hk
      exact elementary_mem_joint Q (complementLift_mem_elementary Q e f he hf hef k hk)
    · apply (Subgroup.closure_le _).mpr
      rintro k ⟨u,hu,rfl⟩
      change complementLift Q e f he hf hef (reflectionElement (complementForm Q e f) u hu) ∈ elementaryReflectionSubgroup Q
      rw [complementLift_reflection]
      exact reflection_mem_joint Q (reflectionElement_mem Q u.val hu)
  exact hle hg

variable {Q}
/-- Joint generation transports through an actual quadratic-space isometry. -/
theorem isometryTransport_mem_elementaryReflection {R : QuadraticForm F W}
    (i : Q.IsometryEquiv R) (g : quadraticIsometrySubgroup Q)
    (hg : g ∈ elementaryReflectionSubgroup Q) :
    isometryGroupTransport i g ∈ elementaryReflectionSubgroup R := by
  have hle : elementaryReflectionSubgroup Q ≤
      (elementaryReflectionSubgroup R).comap (isometryGroupTransport i).toMonoidHom := by
    apply sup_le
    · apply (Subgroup.closure_le _).mpr
      rintro k ⟨u,v,hu,huv,rfl⟩
      have hiu : R (i u) = 0 := (i.map_app u).trans hu
      have hiuv : R.polarBilin (i u) (i v) = 0 :=
        (isometry_between_polar Q R i u v).trans huv
      have ht : isometryGroupTransport i (siegelElement Q u v hu huv) =
          siegelElement R (i u) (i v) hiu hiuv := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        change i (siegel Q u v (i.symm x)) = siegel R (i u) (i v) x
        conv_rhs => rw [← i.apply_symm_apply x]
        simp only [siegel, map_sub, map_add, map_smul,
          isometry_between_polar Q R i, i.map_app]
      change isometryGroupTransport i (siegelElement Q u v hu huv) ∈
        elementaryReflectionSubgroup R
      rw [ht]
      exact elementary_mem_joint R (siegelElement_mem R _ _ _ _)
    · apply (Subgroup.closure_le _).mpr
      rintro k ⟨a,ha,rfl⟩
      have hia : R (i a) ≠ 0 := by rw [i.map_app]; exact ha
      have ht : isometryGroupTransport i (reflectionElement Q a ha) =
          reflectionElement R (i a) hia := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        change i (reflectionLinear Q a ha (i.symm x)) = reflectionLinear R (i a) hia x
        simp only [reflectionLinear_apply, map_sub, map_smul, i.map_app]
        have hp := isometry_between_polar Q R i (i.symm x) a
        rw [i.apply_symm_apply] at hp
        rw [hp, i.apply_symm_apply]
      change isometryGroupTransport i (reflectionElement Q a ha) ∈ elementaryReflectionSubgroup R
      rw [ht]
      exact reflection_mem_joint R (reflectionElement_mem R (i a) hia)
  exact hle hg

private theorem radicalD_eq_bot {n : ℕ} : (formD n F).radical = ⊥ := by
  apply bot_unique
  intro x hx
  rw [Submodule.mem_bot]
  apply polarD_separating x
  intro w
  exact LinearMap.congr_fun hx.2 w

/-- Uniform split-D joint generation, proved by reduction through actual complements. -/
theorem elementary_sup_reflectionsD_eq_top (n : ℕ) :
    elementaryReflectionSubgroup (formD n F) = ⊤ := by
  induction n with
  | zero =>
    apply top_unique
    intro g _
    have hg : g = 1 := Subtype.ext (Subsingleton.elim _ _)
    rw [hg]
    exact (elementaryReflectionSubgroup _).one_mem
  | succ n ih =>
    apply top_unique
    intro g _
    let Q := formD (n+1) F
    obtain ⟨a,ha,hae,haf⟩ := elementaryReflection_pair_transport Q radicalD_eq_bot
      (ClassicalOrthogonal.e 0) (ClassicalOrthogonal.f 0)
      (g.val (ClassicalOrthogonal.e 0)) (g.val (ClassicalOrthogonal.f 0))
      (formD_e 0) (formD_f 0) ((isometry_preserves Q g _).trans (formD_e 0))
      ((isometry_preserves Q g _).trans (formD_f 0)) (polarD_ef 0)
      ((isometry_polar Q (isometryCarrierEquiv Q g) _ _).trans (polarD_ef 0))
    let k := a⁻¹*g
    have hke : k.val (ClassicalOrthogonal.e 0) = ClassicalOrthogonal.e 0 := by
      change a.val.symm (g.val (ClassicalOrthogonal.e 0)) = ClassicalOrthogonal.e 0
      rw [← hae,a.val.symm_apply_apply]
    have hkf : k.val (ClassicalOrthogonal.f 0) = ClassicalOrthogonal.f 0 := by
      change a.val.symm (g.val (ClassicalOrthogonal.f 0)) = ClassicalOrthogonal.f 0
      rw [← haf,a.val.symm_apply_apply]
    let t : pairStabilizer Q (ClassicalOrthogonal.e 0) (ClassicalOrthogonal.f 0) := ⟨k,hke,hkf⟩
    let c := pairRestriction Q (ClassicalOrthogonal.e 0) (ClassicalOrthogonal.f 0) t
    let i := standardComplementD (n := n) (F := F)
    have hc : c ∈ elementaryReflectionSubgroup (complementForm Q
        (ClassicalOrthogonal.e 0) (ClassicalOrthogonal.f 0)) := by
      have hcn : isometryGroupTransport i c ∈ elementaryReflectionSubgroup (formD n F) := by
        rw [ih]
        trivial
      have hback := isometryTransport_mem_elementaryReflection i.symm _ hcn
      have heq : isometryGroupTransport i.symm (isometryGroupTransport i c) = c := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        change i.symm (i (c.val (i.symm (i x)))) = c.val x
        rw [i.symm_apply_apply,i.symm_apply_apply]
      rwa [heq] at hback
    have hk := complementLift_mem_elementaryReflection Q (ClassicalOrthogonal.e 0)
      (ClassicalOrthogonal.f 0) (formD_e 0) (formD_f 0) (polarD_ef 0) c hc
    have heq : complementLift Q (ClassicalOrthogonal.e 0) (ClassicalOrthogonal.f 0)
        (formD_e 0) (formD_f 0) (polarD_ef 0) c = k :=
      congrArg Subtype.val ((pairStabilizerEquiv Q (ClassicalOrthogonal.e 0)
        (ClassicalOrthogonal.f 0) (formD_e 0) (formD_f 0) (polarD_ef 0)).symm_apply_apply t)
    rw [heq] at hk
    have hg := (elementaryReflectionSubgroup Q).mul_mem ha hk
    change a*(a⁻¹*g) ∈ elementaryReflectionSubgroup Q at hg
    simpa only [mul_inv_cancel_left] using hg
end ClassicalOrthogonal.ReflectionGeneration
