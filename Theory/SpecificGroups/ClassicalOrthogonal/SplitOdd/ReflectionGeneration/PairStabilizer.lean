/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.Complement

/-!
# The hyperbolic-pair stabilizer and elementary extension

Adapted from `Atlas/LinearGroups/Orthogonal/{PairStabilizer,
ComplementElementaryLift}.lean`. Restriction identifies the full pointwise
pair stabilizer with the full complement isometry group. Extending a Siegel
transformation gives its same ambient formula, so elementary membership
survives extension. Imports and namespaces are narrowed for CFSG / Lean 4.33.
-/

@[expose] public noncomputable section
universe u
open Theory.AlgebraicGroup

namespace ClassicalOrthogonal.ReflectionGeneration
open ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (e f : V)

def pairStabilizer : Subgroup (quadraticIsometrySubgroup Q) where
  carrier := {g | g.val e = e ∧ g.val f = f}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' {g h} hg hh := by
    constructor
    · change g.val (h.val e) = e
      rw [hh.1, hg.1]
    · change g.val (h.val f) = f
      rw [hh.2, hg.2]
  inv_mem' {g} hg := by
    constructor
    · change g.val.symm e = e
      exact g.val.symm_apply_eq.mpr hg.1.symm
    · change g.val.symm f = f
      exact g.val.symm_apply_eq.mpr hg.2.symm

/-- Restrict every full pair-fixer to the actual perpendicular complement. -/
def pairRestriction : pairStabilizer Q e f →* quadraticIsometrySubgroup (complementForm Q e f) where
  toFun g := (isometryCarrierEquiv _).symm
    (complementTransport Q ((isometryCarrierEquiv Q) g.val) e f e f g.prop.1 g.prop.2)
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rfl

variable (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)

include he hf hef in
theorem pairRestriction_injective : Function.Injective (pairRestriction Q e f) := by
  intro g h hgh
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  let s := split Q e f he hf hef
  have hx := s.symm_apply_apply x
  change (s x).1.1 • e + (s x).1.2 • f + (s x).2.val = x at hx
  have hw : g.val.val (s x).2.val = h.val.val (s x).2.val := by
    have hr := congrArg (fun k : quadraticIsometrySubgroup (complementForm Q e f) =>
      (k.val (s x).2).val) hgh
    exact hr
  calc
    g.val.val x = g.val.val ((s x).1.1 • e + (s x).1.2 • f + (s x).2.val) := congrArg _ hx.symm
    _ = h.val.val ((s x).1.1 • e + (s x).1.2 • f + (s x).2.val) := by
      simp only [map_add, map_smul, g.prop.1, g.prop.2, h.prop.1, h.prop.2, hw]
    _ = h.val.val x := congrArg _ hx

include he hf hef in
theorem pairRestriction_surjective : Function.Surjective (pairRestriction Q e f) := by
  intro k
  let ki := (isometryCarrierEquiv _ k)
  let g := complementExtension Q e f he hf hef ki
  have hge : g e = e := complementExtension_fix_e Q e f he hf hef ki
  have hgf : g f = f := complementExtension_fix_f Q e f he hf hef ki
  refine ⟨⟨(isometryCarrierEquiv Q).symm g, hge, hgf⟩, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  exact complementExtension_apply Q e f he hf hef ki x

/-- The full stabilizer, not merely a displayed subgroup, is the complement isometry group. -/
def pairStabilizerEquiv : pairStabilizer Q e f ≃* quadraticIsometrySubgroup (complementForm Q e f) :=
  MulEquiv.ofBijective (pairRestriction Q e f)
    ⟨pairRestriction_injective Q e f he hf hef, pairRestriction_surjective Q e f he hf hef⟩

end ClassicalOrthogonal.ReflectionGeneration

namespace ClassicalOrthogonal.ReflectionGeneration
open ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (e f : V)
variable (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)

/-- Extend a complement isometry by fixing the displayed hyperbolic pair. -/
def complementLift : quadraticIsometrySubgroup (complementForm Q e f) →* quadraticIsometrySubgroup Q :=
  (pairStabilizer Q e f).subtype.comp
    (pairStabilizerEquiv Q e f he hf hef).symm.toMonoidHom

theorem complementLift_fix_e (g : quadraticIsometrySubgroup (complementForm Q e f)) :
    (complementLift Q e f he hf hef g).val e = e :=
  ((pairStabilizerEquiv Q e f he hf hef).symm g).prop.1

theorem complementLift_fix_f (g : quadraticIsometrySubgroup (complementForm Q e f)) :
    (complementLift Q e f he hf hef g).val f = f :=
  ((pairStabilizerEquiv Q e f he hf hef).symm g).prop.2

theorem complementLift_apply (g : quadraticIsometrySubgroup (complementForm Q e f))
    (x : complement Q e f) :
    (complementLift Q e f he hf hef g).val x.val = (g.val x).val := by
  have h := (pairStabilizerEquiv Q e f he hf hef).apply_symm_apply g
  exact congrArg (fun k : quadraticIsometrySubgroup (complementForm Q e f) => (k.val x).val) h

theorem complementLift_injective : Function.Injective (complementLift Q e f he hf hef) := by
  intro g h hgh
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  rw [← complementLift_apply Q e f he hf hef g x,
    ← complementLift_apply Q e f he hf hef h x, hgh]

/-- Extension carries each actual complement Siegel transformation to its ambient formula. -/
theorem complementLift_siegel (u v : complement Q e f)
    (hu : (complementForm Q e f) u = 0)
    (huv : (complementForm Q e f).polarBilin u v = 0) :
    complementLift Q e f he hf hef (siegelElement (complementForm Q e f) u v hu huv) =
      siegelElement Q u.val v.val hu ((complementForm_polar Q e f u v).symm.trans huv) := by
  have he_u : Q.polarBilin e u.val = 0 := (polar_swap Q e u.val).trans u.prop.1
  have he_v : Q.polarBilin e v.val = 0 := (polar_swap Q e v.val).trans v.prop.1
  have hf_u : Q.polarBilin f u.val = 0 := (polar_swap Q f u.val).trans u.prop.2
  have hf_v : Q.polarBilin f v.val = 0 := (polar_swap Q f v.val).trans v.prop.2
  let s := siegelElement Q u.val v.val hu ((complementForm_polar Q e f u v).symm.trans huv)
  have hse : s.val e = e := by
    change siegel Q u.val v.val e = e
    simp [siegel, he_u, he_v]
  have hsf : s.val f = f := by
    change siegel Q u.val v.val f = f
    simp [siegel, hf_u, hf_v]
  let t : pairStabilizer Q e f := ⟨s, hse, hsf⟩
  have ht : pairRestriction Q e f t = siegelElement (complementForm Q e f) u v hu huv := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change siegel Q u.val v.val x.val = (siegel (complementForm Q e f) u v x).val
    simp only [siegel, complementForm_polar]
    rfl
  have hi : (pairStabilizerEquiv Q e f he hf hef).symm
      (siegelElement (complementForm Q e f) u v hu huv) = t := by
    apply (pairStabilizerEquiv Q e f he hf hef).injective
    exact ((pairStabilizerEquiv Q e f he hf hef).apply_symm_apply _).trans ht.symm
  exact congrArg Subtype.val hi

/-- The full complement elementary subgroup embeds in the ambient elementary subgroup. -/
theorem complementLift_maps_elementary :
    (elementarySubgroup (complementForm Q e f)).map (complementLift Q e f he hf hef) ≤
      elementarySubgroup Q := by
  rw [Subgroup.map_le_iff_le_comap]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨u, v, hu, huv, rfl⟩
  change complementLift Q e f he hf hef
    (siegelElement (complementForm Q e f) u v hu huv) ∈ elementarySubgroup Q
  rw [complementLift_siegel Q e f he hf hef]
  exact siegelElement_mem Q _ _ _ _

/-- An elementwise version suitable for geometric orbit arguments. -/
theorem complementLift_mem_elementary (g : quadraticIsometrySubgroup (complementForm Q e f))
    (hg : g ∈ elementarySubgroup (complementForm Q e f)) :
    complementLift Q e f he hf hef g ∈ elementarySubgroup Q :=
  complementLift_maps_elementary Q e f he hf hef ⟨g, hg, rfl⟩


end ClassicalOrthogonal.ReflectionGeneration
