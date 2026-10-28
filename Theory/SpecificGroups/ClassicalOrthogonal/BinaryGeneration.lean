/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
The hyperbolic-pair induction uses the CFSG adaptation of
Atlas/LinearGroups/Orthogonal/ElementaryReflectionGeneration.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917. The conjugation and reflection-pair
arguments generalize CFSG's BinaryEightObstruction/DerivedBound.lean.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.JointGeneration
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.SiegelReflections
public import Theory.GroupTheory.SolvableResidual
public import Mathlib.Algebra.Field.ZMod

/-!
# Binary orthogonal generation on an arbitrary quadratic space

Joint generation by Siegel transformations and nonsingular reflections follows
by splitting hyperbolic planes until the form is anisotropic. In the binary
anisotropic remainder, a nonzero vector and any polar partner determine an
isometry, and reflections give every such isometry. This induction includes
the exceptional split four-space without asserting reflection generation there.

In dimension at least five, Siegel transformations are products of reflections.
Conversely a common nonsingular perpendicular vector shows that every pair of
reflections is elementary. The full group is therefore elementary-by-cyclic,
and its solvable residual lies in the actual Siegel-generated subgroup.
No coordinate-model, perfectness or simplicity premise is assumed.

The G.12 quadratic-branch consumer uses this inclusion for its original form
and original point radicals. Source: Aschbacher--Smith G.12.10, printed p.373;
the licensed hyperbolic-pair and reflection calculations cited above.
-/

public noncomputable section
open Theory.AlgebraicGroup Subgroup Module
open ClassicalOrthogonal.Quadratic ClassicalOrthogonal.ReflectionGeneration
namespace ClassicalOrthogonal.BinaryGeneration
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable (Q : QuadraticForm (ZMod 2) V)

private theorem bit {a : ZMod 2} (ha : a≠0) : a=1 :=
  (by decide : ∀ a : ZMod 2,a=0 ∨ a=1) a |>.resolve_left ha

private theorem double (v : V) : v+v=0 := by
  simpa only [two_smul,zero_smul] using congrArg (fun c : ZMod 2 => c • v)
    (show (2 : ZMod 2)=0 from by decide)

private theorem aniso_perp (han : Q.Anisotropic) {u w : V} (hu : u≠0)
    (hw : Q.polarBilin u w=0) : w=0 ∨ w=u := by
  by_cases hw0 : w=0
  · exact Or.inl hw0
  right
  have hqu : Q u=1 := bit (fun hz => hu (han u hz))
  have hqw : Q w=1 := bit (fun hz => hw0 (han w hz))
  have hz : Q (u+w)=0 := by
    rw [QuadraticMap.map_add Q]
    change Q u+Q w+Q.polarBilin u w=0
    rw [hqu,hqw,hw]
    decide
  have he := congrArg (fun x : V => u+x) (han (u+w) hz)
  simpa only [← add_assoc,double,zero_add,add_zero] using he

private theorem aniso_pair_ext (han : Q.Anisotropic) {u v : V}
    (hu : u≠0) (huv : Q.polarBilin u v=1)
    {a b : V ≃ₗ[ZMod 2] V} (hau : a u=b u) (hav : a v=b v) : a=b := by
  apply LinearEquiv.ext
  intro x
  let z := x-Q.polarBilin u x • v
  have hz : Q.polarBilin u z=0 := by simp only [z,map_sub,map_smul,huv,smul_eq_mul,mul_one,sub_self]
  have haz : a z=b z := by
    rcases aniso_perp Q han hu hz with he|he
    · rw [he,map_zero,map_zero]
    · rw [he,hau]
  change a (x-Q.polarBilin u x • v)=b (x-Q.polarBilin u x • v) at haz
  simpa only [map_sub,map_smul,hav,sub_left_inj] using haz

private theorem aniso_fix_mem (han : Q.Anisotropic)
    (hQ : Q.polarBilin.Nondegenerate) {u : V} (hu : u≠0)
    (g : quadraticIsometrySubgroup Q) (hgu : g.val u=u) :
    g∈reflectionSubgroup Q := by
  obtain ⟨v,huv⟩ := exists_normalized_partner Q u (fun hh => hu (hQ.1 u hh))
  have hp : Q.polarBilin u (g.val v-v)=0 := by
    have h := isometry_polar Q (isometryCarrierEquiv Q g) u v
    change Q.polarBilin (g.val u) (g.val v)=Q.polarBilin u v at h
    rw [hgu] at h
    rw [map_sub,h,sub_self]
  rcases aniso_perp Q han hu hp with hv|hv
  · have he : g=1 := Subtype.ext (aniso_pair_ext Q han hu huv hgu (sub_eq_zero.mp hv))
    rw [he]
    exact (reflectionSubgroup Q).one_mem
  · have hqu : Q u≠0 := fun hz => hu (han u hz)
    have he : g=reflectionElement Q u hqu := by
      apply Subtype.ext
      apply aniso_pair_ext Q han hu huv
      · change g.val u=reflectionLinear Q u hqu u
        rw [hgu,reflectionLinear_apply,polar_self,show (2 : ZMod 2)=0 from by decide,
          zero_mul,mul_zero,zero_smul,sub_zero]
      · change g.val v=reflectionLinear Q u hqu v
        rw [reflectionLinear_apply,bit hqu,inv_one,one_mul,polar_swap Q v u,huv,
          one_smul,ZModModule.sub_eq_add]
        exact (sub_eq_iff_eq_add.mp hv).trans (add_comm u v)
    rw [he]
    exact reflectionElement_mem _ _ _

private theorem anisotropic_reflections (han : Q.Anisotropic)
    (hQ : Q.polarBilin.Nondegenerate) : reflectionSubgroup Q=⊤ := by
  apply top_unique
  intro g _
  by_cases hz : ∀ u : V,u=0
  · have he : g=1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change g.val x=x
      rw [hz x,map_zero]
    rw [he]
    exact (reflectionSubgroup Q).one_mem
  obtain ⟨u,hu⟩ := not_forall.mp hz
  by_cases hgu : g.val u=u
  · exact aniso_fix_mem Q han hQ hu g hgu
  have huq : Q u=1 := bit (fun hh => hu (han u hh))
  have hgq : Q (g.val u)=1 := (isometry_preserves Q g u).trans huq
  have huw : u+g.val u≠0 := by
    intro he
    have hh := congrArg (fun z : V => u+z) he
    exact hgu (by simpa only [← add_assoc,double,zero_add,add_zero] using hh)
  have hq : Q (u+g.val u)≠0 := fun hh => huw (han _ hh)
  have hb : Q.polarBilin u (g.val u)=1 := by
    have hh := QuadraticMap.map_add Q u (g.val u)
    change Q (u+g.val u)=Q u+Q (g.val u)+Q.polarBilin u (g.val u) at hh
    rw [bit hq,huq,hgq,show (1 : ZMod 2)+1=0 from by decide,zero_add] at hh
    exact hh.symm
  let r := reflectionElement Q (u+g.val u) hq
  have hru : r.val u=g.val u := by
    change reflectionLinear Q (u+g.val u) hq u=g.val u
    rw [reflectionLinear_apply,bit hq,inv_one,one_mul,map_add,polar_self,
      show (2 : ZMod 2)=0 from by decide,zero_mul,zero_add,hb,one_smul,ZModModule.sub_eq_add,
      ← add_assoc,double,zero_add]
  have hf : (r⁻¹*g).val u=u := by
    change r.val.symm (g.val u)=u
    rw [← hru,r.val.symm_apply_apply]
  have hm := (reflectionSubgroup Q).mul_mem (reflectionElement_mem Q _ hq)
    (aniso_fix_mem Q han hQ hu (r⁻¹*g) hf)
  change r*(r⁻¹*g) ∈ reflectionSubgroup Q at hm
  simpa only [mul_inv_cancel_left] using hm

variable [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
private theorem complement_nondegenerate (hQ : Q.polarBilin.Nondegenerate)
    (e f : V) (he : Q e=0) (hf : Q f=0) (hef : Q.polarBilin e f=1) :
    (complementForm Q e f).polarBilin.Nondegenerate := by
  have hinj : (complementForm Q e f).polarBilin.SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    apply hQ.1 x.val
    intro y
    have hh := hx (split Q e f he hf hef y).2
    rw [complementForm_polar] at hh
    have hy := (split Q e f he hf hef).symm_apply_apply y
    change Q.polarBilin y f • e+Q.polarBilin y e • f+
      ((split Q e f he hf hef y).2 : V)=y at hy
    have hxe : Q.polarBilin x.val e=0 := x.property.1
    have hxf : Q.polarBilin x.val f=0 := x.property.2
    rw [← hy,map_add,map_add,map_smul,map_smul,hxe,hxf,
      smul_zero,smul_zero,zero_add,zero_add,hh]
  exact ⟨hinj,fun x hx => hinj x (fun y => (polar_swap _ x y).trans (hx y))⟩

/-- Every binary polar-nondegenerate orthogonal group is generated jointly
by its Siegel transformations and nonsingular reflections. -/
theorem joint_eq_top (hQ : Q.polarBilin.Nondegenerate) :
    elementaryReflectionSubgroup Q=⊤ := by
  generalize hd : finrank (ZMod 2) V=d
  induction d using Nat.strong_induction_on generalizing V with
  | h d ih =>
    by_cases han : Q.Anisotropic
    · rw [elementaryReflectionSubgroup,anisotropic_reflections Q han hQ,sup_top_eq]
    obtain ⟨e,he,he0⟩ : ∃ e : V,Q e=0 ∧ e≠0 := by
      have hh : ¬∀ e : V,Q e=0 → e=0 := han
      push Not at hh
      exact hh
    obtain ⟨f0,hf0⟩ := exists_normalized_partner Q e (fun hh => he0 (hQ.1 e hh))
    let f := f0-Q f0 • e
    have hf : Q f=0 := (partner_correction Q e f0 he hf0).1
    have hef : Q.polarBilin e f=1 := (partner_correction Q e f0 he hf0).2
    have hdim := finrank_complement Q e f he hf hef
    have hc := ih (finrank (ZMod 2) (complement Q e f)) (by omega)
      (complementForm Q e f) (complement_nondegenerate Q hQ e f he hf hef) rfl
    have hrad : Q.radical=⊥ := by
      apply bot_unique
      intro x hx
      exact hQ.1 x (fun y => LinearMap.congr_fun hx.2 y)
    apply top_unique
    intro g _
    obtain ⟨a,ha,hae,haf⟩ := elementaryReflection_pair_transport Q hrad e f
      (g.val e) (g.val f) he hf ((isometry_preserves Q g e).trans he)
      ((isometry_preserves Q g f).trans hf) hef
      ((isometry_polar Q (isometryCarrierEquiv Q g) e f).trans hef)
    let k := a⁻¹*g
    have hke : k.val e=e := by
      change a.val.symm (g.val e)=e
      rw [← hae,a.val.symm_apply_apply]
    have hkf : k.val f=f := by
      change a.val.symm (g.val f)=f
      rw [← haf,a.val.symm_apply_apply]
    let t : pairStabilizer Q e f := ⟨k,hke,hkf⟩
    let c := pairRestriction Q e f t
    have hcm : c∈elementaryReflectionSubgroup (complementForm Q e f) := hc.ge (mem_top _)
    have hk := complementLift_mem_elementaryReflection Q e f he hf hef c hcm
    have heq : complementLift Q e f he hf hef c=k :=
      congrArg Subtype.val ((pairStabilizerEquiv Q e f he hf hef).symm_apply_apply t)
    rw [heq] at hk
    have hm := (elementaryReflectionSubgroup Q).mul_mem ha hk
    change a*(a⁻¹*g) ∈ elementaryReflectionSubgroup Q at hm
    simpa only [mul_inv_cancel_left] using hm

/-- Nonsingular reflections generate every binary polar-nondegenerate
orthogonal group of dimension at least five, in either Witt type. -/
theorem reflections_eq_top (hQ : Q.polarBilin.Nondegenerate)
    (hd : 5≤finrank (ZMod 2) V) : reflectionSubgroup Q=⊤ := by
  have h := joint_eq_top Q hQ
  rwa [elementaryReflectionSubgroup,
    sup_eq_right.mpr (elementary_le_reflections_stable Q hQ hd)] at h

/- Conjugation carries an actual Siegel generator to an actual Siegel generator. -/
omit [FiniteDimensional (ZMod 2) V] in
theorem siegelElement_conj (g : quadraticIsometrySubgroup Q) (u v : V)
    (hu : Q u = 0) (huv : Q.polarBilin u v = 0) :
    g * siegelElement Q u v hu huv * g⁻¹ =
      siegelElement Q (g.val u) (g.val v)
        ((isometryCarrierEquiv Q g).map_app u |>.trans hu)
        ((isometry_polar Q (isometryCarrierEquiv Q g) u v).trans huv) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change g.val (siegel Q u v (g.val.symm x)) =
    siegel Q (g.val u) (g.val v) x
  have h := siegel_covariant Q (isometryCarrierEquiv Q g) u v (g.val.symm x)
  change g.val (siegel Q u v (g.val.symm x)) =
    siegel Q (g.val u) (g.val v) (g.val (g.val.symm x)) at h
  simpa only [LinearEquiv.apply_symm_apply] using h

instance elementary_normal : (elementarySubgroup Q).Normal := by
  constructor
  intro x hx g
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, v, hu, huv, rfl⟩ := hx
    rw [siegelElement_conj Q]
    exact siegelElement_mem _ _ _ _ _
  | one => simp
  | mul x y _ _ ihx ihy =>
    have he : g * (x*y) * g⁻¹ = (g*x*g⁻¹) * (g*y*g⁻¹) := by group
    rw [he]
    exact (elementarySubgroup Q).mul_mem ihx ihy
  | inv x _ ih =>
    have he : g * x⁻¹ * g⁻¹ = (g*x*g⁻¹)⁻¹ := by group
    rw [he]
    exact (elementarySubgroup Q).inv_mem ih

omit [FiniteDimensional (ZMod 2) V] in
private theorem reflection_inv (a : V) (ha : Q a ≠ 0) :
    (reflectionElement Q a ha)⁻¹ = reflectionElement Q a ha :=
  Subtype.ext (Module.reflection_inv (reflectionFunctional_self Q a ha))

omit [FiniteDimensional (ZMod 2) V] in
private theorem perpendicular_reflection_pair_mem (a b : V)
    (ha : Q a ≠ 0) (hb : Q b ≠ 0)
    (hab : Q.polarBilin a b = 0) :
    reflectionElement Q b hb * reflectionElement Q a ha ∈ elementarySubgroup Q := by
  have hqa : Q a = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ ha
  have hqb : Q b = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ hb
  have hba : Q.polarBilin b a = 0 := (polar_swap Q b a).trans hab
  have hu : Q (b+a) = 0 := by
    rw [QuadraticMap.map_add Q]
    change Q b + Q a + Q.polarBilin b a = 0
    rw [hqb, hqa, hba]
    decide
  have hua : Q.polarBilin (b+a) a = 0 := by
    rw [map_add, LinearMap.add_apply, hba, polar_self, hqa]
    decide
  have hv : a + Q a • (b+a) = b := by
    rw [hqa, one_smul]
    have haa : a+a = 0 := ZModModule.add_self a
    calc
      a+(b+a) = b+(a+a) := by abel
      _ = b := by rw [haa, add_zero]
  have he := siegelElement_reflection_factor Q (b+a) a hu hua ha
  have hm := siegelElement_mem Q (b+a) a hu hua
  rw [he] at hm
  simpa only [hv] using hm

/- Any two nonsingular reflections have elementary product. -/
theorem reflection_pair_mem_elementary (hQ : Q.polarBilin.Nondegenerate)
    (hd : 5 ≤ finrank (ZMod 2) V) (a b : V)
    (ha : Q a ≠ 0) (hb : Q b ≠ 0) :
    reflectionElement Q b hb * reflectionElement Q a ha ∈ elementarySubgroup Q := by
  obtain ⟨c, hc, hac, hbc⟩ := exists_anisotropic_perpendicular_pair Q
    hQ hd a b
  have h1 := perpendicular_reflection_pair_mem Q c b hc hb
    ((polar_swap Q c b).trans hbc)
  have h2 := perpendicular_reflection_pair_mem Q a c ha hc hac
  have hm := (elementarySubgroup Q).mul_mem h1 h2
  have hc2 : reflectionElement Q c hc * reflectionElement Q c hc = 1 := by
    calc
      reflectionElement Q c hc * reflectionElement Q c hc =
          reflectionElement Q c hc * (reflectionElement Q c hc)⁻¹ :=
        congrArg (fun x => reflectionElement Q c hc * x) (reflection_inv Q c hc).symm
      _ = 1 := mul_inv_cancel _
  have heq : (reflectionElement Q b hb * reflectionElement Q c hc) *
      (reflectionElement Q c hc * reflectionElement Q a ha) =
      reflectionElement Q b hb * reflectionElement Q a ha := by
    calc
      _ = reflectionElement Q b hb *
          (reflectionElement Q c hc * reflectionElement Q c hc) *
            reflectionElement Q a ha := by group
      _ = _ := by rw [hc2, mul_one]
  exact heq ▸ hm


/-- The full binary orthogonal commutator is generated inside the Siegel
subgroup in dimension at least five. No simplicity assertion is needed. -/
theorem commutator_le_elementary (hQ : Q.polarBilin.Nondegenerate)
    (hd : 5 ≤ finrank (ZMod 2) V) :
    commutator (quadraticIsometrySubgroup Q) ≤ elementarySubgroup Q := by
  obtain ⟨a,ha,_,_⟩ := exists_anisotropic_perpendicular_pair Q hQ hd 0 0
  let r := reflectionElement Q a ha
  let H : Subgroup (quadraticIsometrySubgroup Q) := elementarySubgroup Q ⊔ Subgroup.zpowers r
  have hr : reflectionSubgroup Q ≤ H := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨b,hb,rfl⟩
    change reflectionElement Q b hb ∈ H
    have hm : reflectionElement Q b hb*r ∈ H :=
      (show elementarySubgroup Q ≤ H from le_sup_left)
        (reflection_pair_mem_elementary Q hQ hd a b ha hb)
    have hi : r⁻¹∈H := H.inv_mem
      ((show Subgroup.zpowers r ≤ H from le_sup_right) (Subgroup.mem_zpowers r))
    simpa only [mul_assoc,mul_inv_cancel,mul_one] using H.mul_mem hm hi
  have ht : elementarySubgroup Q ⊔ Subgroup.zpowers r=⊤ :=
    top_unique (reflections_eq_top Q hQ hd ▸ hr)
  exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top ht inferInstance

/-- The full orthogonal solvable residual lies in the actual Siegel-generated
subgroup, uniformly for the two binary quadratic types. -/
theorem solvableResidual_le_elementary (hQ : Q.polarBilin.Nondegenerate)
    (hd : 5 ≤ finrank (ZMod 2) V) :
    Subgroup.solvableResidual (quadraticIsometrySubgroup Q) ≤ elementarySubgroup Q :=
  (show Subgroup.solvableResidual (quadraticIsometrySubgroup Q) ≤
    commutator (quadraticIsometrySubgroup Q) from
    Subgroup.solvableResidual_le_derivedSeries 1).trans (commutator_le_elementary Q hQ hd)

end ClassicalOrthogonal.BinaryGeneration
