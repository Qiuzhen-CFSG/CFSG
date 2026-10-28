/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The conjugation and reflection-generation argument is adapted from
Atlas/LinearGroups/Orthogonal/ElementaryNormal.lean and
Atlas/LinearGroups/Orthogonal/EvenDReflectionIdentification.lean.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration
import Mathlib.GroupTheory.IsPerfect
import Mathlib.Tactic.Group

/-!
# The full binary split-eight commutator bound

The literal Siegel-generated subgroup of the full isometry group of
`formD 4 (ZMod 2)` contains every product of two nonsingular reflections.
Indeed, a common nonsingular perpendicular vector reduces the general pair to
two perpendicular pairs, and a perpendicular pair is one Siegel transformation.
The stable reflection-generation theorem then makes the elementary subgroup
elementary-by-cyclic, so the full commutator is contained in it.  This is the
intrinsic `Ω₈⁺(2)` image comparison input; no order, recognition, parity or
index statement is used.

Source: Aschbacher, *Sporadic Groups* (1994), 46.1, printed p.251.
The reflection and normality ingredients are adapted from the ATLAS sources
named above.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup
open ClassicalOrthogonal.Quadratic
open ClassicalOrthogonal.ReflectionGeneration

namespace ClassicalOrthogonal.BinaryEightObstruction

abbrev K := ZMod 2
abbrev V := VectorD 4 K
abbrev Q := formD 4 K
abbrev FullGroup := quadraticIsometrySubgroup Q

/- Conjugation carries an actual Siegel generator to an actual Siegel generator. -/
theorem siegelElement_conj (g : FullGroup) (u v : V)
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
    rw [siegelElement_conj]
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

private theorem reflection_inv (a : V) (ha : Q a ≠ 0) :
    (reflectionElement Q a ha)⁻¹ = reflectionElement Q a ha :=
  Subtype.ext (Module.reflection_inv (reflectionFunctional_self Q a ha))

private theorem perpendicular_reflection_pair_mem (a b : V)
    (ha : Q a ≠ 0) (hb : Q b ≠ 0)
    (hab : Q.polarBilin a b = 0) :
    reflectionElement Q b hb * reflectionElement Q a ha ∈ elementarySubgroup Q := by
  have hqa : Q a = 1 := (by decide : ∀ c : K, c ≠ 0 → c = 1) _ ha
  have hqb : Q b = 1 := (by decide : ∀ c : K, c ≠ 0 → c = 1) _ hb
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
theorem reflection_pair_mem_elementary (a b : V)
    (ha : Q a ≠ 0) (hb : Q b ≠ 0) :
    reflectionElement Q b hb * reflectionElement Q a ha ∈ elementarySubgroup Q := by
  have hd : 5 ≤ Module.finrank K V := by
    rw [vectorD_finrank]
    decide
  obtain ⟨c, hc, hac, hbc⟩ := exists_anisotropic_perpendicular_pair Q
    polarD_nondegenerate hd a b
  have h1 := perpendicular_reflection_pair_mem c b hc hb
    ((polar_swap Q c b).trans hbc)
  have h2 := perpendicular_reflection_pair_mem a c ha hc hac
  have hm := (elementarySubgroup Q).mul_mem h1 h2
  have hc2 : reflectionElement Q c hc * reflectionElement Q c hc = 1 := by
    calc
      reflectionElement Q c hc * reflectionElement Q c hc =
          reflectionElement Q c hc * (reflectionElement Q c hc)⁻¹ :=
        congrArg (fun x => reflectionElement Q c hc * x) (reflection_inv c hc).symm
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

/- The full group is generated by the elementary subgroup and one cyclic factor. -/
theorem commutator_full_le_elementary :
    commutator FullGroup ≤ elementarySubgroup Q := by
  have hreflection : reflectionSubgroup Q = ⊤ := by
    simpa only [show 1 + 3 = 4 by decide] using
      (reflectionSubgroupD_eq_top_stable (F := K) 1)
  let a : V := e 0 + f 0
  have ha : Q a ≠ 0 := by
    dsimp [a, Q]
    rw [formD_e_add_f]
    decide
  let r := reflectionElement Q a ha
  let H : Subgroup FullGroup := elementarySubgroup Q ⊔ Subgroup.zpowers r
  have hr : reflectionSubgroup Q ≤ H := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨b, hb, rfl⟩
    change reflectionElement Q b hb ∈ H
    have hm : reflectionElement Q b hb * r ∈ H :=
      (show elementarySubgroup Q ≤ H from le_sup_left)
        (reflection_pair_mem_elementary a b ha hb)
    have hi : r⁻¹ ∈ H := H.inv_mem
      ((show Subgroup.zpowers r ≤ H from le_sup_right) (Subgroup.mem_zpowers r))
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using H.mul_mem hm hi
  have htop : elementarySubgroup Q ⊔ Subgroup.zpowers r = ⊤ :=
    top_unique (hreflection ▸ hr)
  exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top htop inferInstance

end ClassicalOrthogonal.BinaryEightObstruction
