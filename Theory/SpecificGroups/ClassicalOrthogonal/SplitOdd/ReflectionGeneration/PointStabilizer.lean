/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
The partner correction is adapted from Atlas/LinearAlgebra/QuadraticPairTransport.lean
and the CFSG adaptation in ReflectionGeneration/JointGeneration.lean.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.PairStabilizer

/-!
# Explicit singular-vector stabilizer factorization

For a normalized hyperbolic pair `(e,f)`, a point-fixer `g` is the product of
one Siegel transformation fixing `e` and the extension of its corrected
restriction to the perpendicular complement. The root parameter is the negative
perpendicular component of `g(f)`. These are literal isometries acting on the
original vector space, in arbitrary characteristic.

If `g` is elementary, the extended complement factor is elementary. Membership
of the restriction itself is a separate obligation: extension alone does not
prove the elementary parabolic theorem. Quadratic-isometry transport preserves
the actual Siegel-generated subgroup, and is provided for that obligation.

Source: the hyperbolic-pair reduction in the licensed ATLAS module named above;
application to the binary octad parabolic in Aschbacher, Sporadic Groups (1994),
25.1(4), 25.2 and 25.5(7), pp.132--134.
-/

@[expose] public noncomputable section
universe u
open Theory.AlgebraicGroup
open ClassicalOrthogonal.Quadratic
namespace ClassicalOrthogonal.ReflectionGeneration
variable {F V W : Type u} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
variable (Q : QuadraticForm F V) (e f : V)
variable (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)

/-- The root parameter is the negative perpendicular component of the new partner. -/
def pointRootParameter (g : quadraticIsometrySubgroup Q) : complement Q e f :=
  -(split Q e f he hf hef (g.val f)).2

def pointRootFactor (g : quadraticIsometrySubgroup Q) : quadraticIsometrySubgroup Q :=
  siegelElement Q e (pointRootParameter Q e f he hf hef g).val he
    ((polar_swap Q e _).trans (pointRootParameter Q e f he hf hef g).prop.1)

theorem pointRootFactor_mem (g : quadraticIsometrySubgroup Q) :
    pointRootFactor Q e f he hf hef g ∈ elementarySubgroup Q :=
  siegelElement_mem _ _ _ _ _

theorem pointRootFactor_fix (g : quadraticIsometrySubgroup Q) :
    (pointRootFactor Q e f he hf hef g).val e = e :=
  siegel_fix Q e (pointRootParameter Q e f he hf hef g).val he
    ((polar_swap Q e _).trans (pointRootParameter Q e f he hf hef g).prop.1)

theorem pointRootFactor_partner (g : quadraticIsometrySubgroup Q) (hge : g.val e = e) :
    (pointRootFactor Q e f he hf hef g).val f = g.val f := by
  let v := g.val f
  let s := split Q e f he hf hef
  let w := (s v).2
  have hw := (mem_complement Q e f w.val).mp w.prop
  have hfw : Q.polarBilin f w.val = 0 := (polar_swap Q f w.val).trans hw.2
  have hv : Q v = 0 := (isometry_preserves Q g f).trans hf
  have hev : Q.polarBilin e v = 1 := by
    have h := isometry_polar Q (isometryCarrierEquiv Q g) e f
    change Q.polarBilin (g.val e) v = _ at h
    rwa [hge, hef] at h
  have hve : Q.polarBilin v e = 1 := (polar_swap Q v e).trans hev
  have hfe : Q.polarBilin f e = 1 := (polar_swap Q f e).trans hef
  have ha : Q.polarBilin v f = -Q w.val := by
    have h := form_split Q e f he hf hef v
    change Q v = Q.polarBilin v f * Q.polarBilin v e + Q w.val at h
    rw [hv, hve, mul_one] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hd := s.symm_apply_apply v
  change Q.polarBilin v f • e + Q.polarBilin v e • f + w.val = v at hd
  rw [ha, hve, one_smul] at hd
  change siegel Q e (-w.val) f = v
  rw [← hd]
  simp only [siegel, map_neg, hfw, hfe, Q.map_neg, neg_zero, zero_smul, one_smul, mul_one]
  module

/-- Removing the displayed root factor fixes both vectors of the chosen pair. -/
def pointPairFactor (g : quadraticIsometrySubgroup Q) (hge : g.val e = e) :
    pairStabilizer Q e f :=
  ⟨(pointRootFactor Q e f he hf hef g)⁻¹ * g, by
    constructor
    · change (pointRootFactor Q e f he hf hef g).val.symm (g.val e) = e
      rw [hge]
      exact (pointRootFactor Q e f he hf hef g).val.symm_apply_eq.mpr
        (pointRootFactor_fix Q e f he hf hef g).symm
    · change (pointRootFactor Q e f he hf hef g).val.symm (g.val f) = f
      rw [← pointRootFactor_partner Q e f he hf hef g hge]
      exact (pointRootFactor Q e f he hf hef g).val.symm_apply_apply f⟩

def pointComplementFactor (g : quadraticIsometrySubgroup Q) (hge : g.val e = e) :
    quadraticIsometrySubgroup (complementForm Q e f) :=
  pairRestriction Q e f (pointPairFactor Q e f he hf hef g hge)

theorem pointComplementFactor_lift (g : quadraticIsometrySubgroup Q) (hge : g.val e = e) :
    complementLift Q e f he hf hef (pointComplementFactor Q e f he hf hef g hge) =
      (pointRootFactor Q e f he hf hef g)⁻¹ * g :=
  congrArg Subtype.val ((pairStabilizerEquiv Q e f he hf hef).symm_apply_apply
    (pointPairFactor Q e f he hf hef g hge))

/-- Actual point-fixer factorization on the original vector space. -/
theorem point_factorization (g : quadraticIsometrySubgroup Q) (hge : g.val e = e) :
    g = pointRootFactor Q e f he hf hef g *
      complementLift Q e f he hf hef (pointComplementFactor Q e f he hf hef g hge) := by
  rw [pointComplementFactor_lift, mul_inv_cancel_left]

theorem pointComplementFactor_lift_mem (g : quadraticIsometrySubgroup Q)
    (hg : g ∈ elementarySubgroup Q) (hge : g.val e = e) :
    complementLift Q e f he hf hef (pointComplementFactor Q e f he hf hef g hge) ∈
      elementarySubgroup Q := by
  rw [pointComplementFactor_lift]
  exact (elementarySubgroup Q).mul_mem
    ((elementarySubgroup Q).inv_mem (pointRootFactor_mem Q e f he hf hef g)) hg

variable {Q} {R : QuadraticForm F W}

theorem isometryTransport_siegel (i : Q.IsometryEquiv R) (u v : V)
    (hu : Q u = 0) (huv : Q.polarBilin u v = 0) :
    isometryGroupTransport i (siegelElement Q u v hu huv) =
      siegelElement R (i u) (i v) ((i.map_app u).trans hu)
        ((isometry_between_polar Q R i u v).trans huv) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change i (siegel Q u v (i.symm x)) = siegel R (i u) (i v) x
  conv_rhs => rw [← i.apply_symm_apply x]
  simp only [siegel, map_sub, map_add, map_smul,
    isometry_between_polar Q R i, i.map_app]

theorem isometryTransport_mem_elementary (i : Q.IsometryEquiv R)
    (g : quadraticIsometrySubgroup Q) (hg : g ∈ elementarySubgroup Q) :
    isometryGroupTransport i g ∈ elementarySubgroup R := by
  have hle : elementarySubgroup Q ≤
      (elementarySubgroup R).comap (isometryGroupTransport i).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro k ⟨u, v, hu, huv, rfl⟩
    change isometryGroupTransport i (siegelElement Q u v hu huv) ∈ elementarySubgroup R
    rw [isometryTransport_siegel]
    exact siegelElement_mem _ _ _ _ _
  exact hle hg

theorem isometryTransport_mem_elementary_iff (i : Q.IsometryEquiv R)
    (g : quadraticIsometrySubgroup Q) :
    isometryGroupTransport i g ∈ elementarySubgroup R ↔ g ∈ elementarySubgroup Q := by
  refine ⟨fun h => ?_, isometryTransport_mem_elementary i g⟩
  have hback := isometryTransport_mem_elementary i.symm _ h
  have heq : isometryGroupTransport i.symm (isometryGroupTransport i g) = g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change i.symm (i (g.val (i.symm (i x)))) = g.val x
    rw [i.symm_apply_apply, i.symm_apply_apply]
  rwa [heq] at hback
end ClassicalOrthogonal.ReflectionGeneration
