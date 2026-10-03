module
public import Theory.GroupTheory.ZStar.OddProductConjugator
public import Mathlib.Algebra.Group.Conj

/-!
# Constancy on products of two conjugacy classes

For a distinguished involution t, suppose its product with each conjugate
has odd order. If each conjugate r of s admits a conjugate replacement r0
commuting with t and preserving the value of f(t*r), then f is constant
on all products of a conjugate of t and a conjugate of s. The function is
defined on actual conjugacy classes; no algebraic structure on its codomain
is used. In particular, the theorem applies to `ConjClassFunction G`.

First conjugate an arbitrary product x*y to t*r. Replace r and s by r0 and
s0 commuting with t. A conjugator a from r0 to s0 sends t back to a second
involution u commuting with r0. The odd-product conjugator from t to u
centralizes r0; composing it with a therefore gives a conjugator from r0
to s0 that centralizes t. Thus t*r0 and t*s0 are conjugate, and the two
replacement equalities give the required constancy.

This is the group-theoretic part of Glauberman Step (V), as formulated in
Feit XII.8.9 after the commuting-replacement input XII.8.8. The proof is
ported from `c3503435:glauberman_zStar/Submission/ZStar/Constancy.lean`.
The historical complex-valued function is generalized to an arbitrary
codomain, retaining its named interface and all group hypotheses.
-/

namespace Glauberman.ZStar.Constancy
open BenderSuzuki.PFAppendixIII

/-- Commuting replacements imply constancy on the product of two conjugacy classes. -/
public theorem classProducts_constant_of_commuting_replacements
    {G A : Type*} [Group G] [Finite G]
    (f : ConjClasses G → A)
    (t s : G) (htI : IsInvolution t)
    (hodd : ∀ g : G, Odd (orderOf ((g * t * g⁻¹) * t)))
    (hreplace : ∀ r : G, r ∈ (ConjClasses.mk s).carrier →
      ∃ r0 : G, r0 ∈ (ConjClasses.mk s).carrier ∧ Commute t r0 ∧
        f (ConjClasses.mk (t * r)) = f (ConjClasses.mk (t * r0))) :
    ∀ x : G, x ∈ (ConjClasses.mk t).carrier →
      ∀ y : G, y ∈ (ConjClasses.mk s).carrier →
        f (ConjClasses.mk (x * y)) = f (ConjClasses.mk (t * s)) := by
  intro x hx y hy
  have htx : IsConj t x := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mp
    exact (ConjClasses.mem_carrier_iff_mk_eq.mp hx).symm
  rcases isConj_iff.mp htx with ⟨g, hg⟩
  let r : G := g⁻¹ * y * g
  have hr : r ∈ (ConjClasses.mk s).carrier := by
    apply ConjClasses.mem_carrier_iff_mk_eq.mpr
    calc
      ConjClasses.mk r = ConjClasses.mk y := by
        apply ConjClasses.mk_eq_mk_iff_isConj.mpr
        apply isConj_iff.mpr
        refine ⟨g, ?_⟩
        dsimp [r]
        group
      _ = ConjClasses.mk s := ConjClasses.mem_carrier_iff_mk_eq.mp hy
  have hxy : ConjClasses.mk (x * y) = ConjClasses.mk (t * r) := by
    symm
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    apply isConj_iff.mpr
    refine ⟨g, ?_⟩
    dsimp [r]
    calc
      g * (t * (g⁻¹ * y * g)) * g⁻¹ = (g * t * g⁻¹) * y := by group
      _ = x * y := by rw [hg]
  obtain ⟨r0, hr0, htr0, hfr⟩ := hreplace r hr
  obtain ⟨s0, hs0, hts0, hfs⟩ := hreplace s ConjClasses.mem_carrier_mk
  have hr0s0 : IsConj r0 s0 := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mp
    exact (ConjClasses.mem_carrier_iff_mk_eq.mp hr0).trans
      (ConjClasses.mem_carrier_iff_mk_eq.mp hs0).symm
  rcases isConj_iff.mp hr0s0 with ⟨a, ha⟩
  let u : G := a⁻¹ * t * a
  have huI : IsInvolution u := by
    simpa only [u, rightConjugateElem] using
      (isInvolution_rightConjugateElem (g := a) htI)
  have hr0u : Commute r0 u := by
    have hr0_eq : r0 = a⁻¹ * s0 * a := by
      calc
        r0 = a⁻¹ * (a * r0 * a⁻¹) * a := by group
        _ = a⁻¹ * s0 * a := by rw [ha]
    rw [hr0_eq]
    change (a⁻¹ * s0 * a) * (a⁻¹ * t * a) =
      (a⁻¹ * t * a) * (a⁻¹ * s0 * a)
    calc
      (a⁻¹ * s0 * a) * (a⁻¹ * t * a) = a⁻¹ * (s0 * t) * a := by group
      _ = a⁻¹ * (t * s0) * a := by rw [hts0.eq]
      _ = (a⁻¹ * t * a) * (a⁻¹ * s0 * a) := by group
  have hut_odd : Odd (orderOf (u * t)) := by
    simpa [u] using hodd a⁻¹
  obtain ⟨z, hzt, hr0z⟩ :=
    exists_conjugator_of_involutions_mul_odd huI htI hut_odd
  have hzcomm : Commute r0 z := hr0z r0 hr0u htr0.symm
  let c : G := a * z
  have hct : c * t * c⁻¹ = t := by
    dsimp [c]
    calc
      a * z * t * (a * z)⁻¹ = a * (z * t * z⁻¹) * a⁻¹ := by group
      _ = a * u * a⁻¹ := by rw [hzt]
      _ = t := by simp [u, mul_assoc]
  have hcr0 : c * r0 * c⁻¹ = s0 := by
    dsimp [c]
    calc
      a * z * r0 * (a * z)⁻¹ = a * (z * r0 * z⁻¹) * a⁻¹ := by group
      _ = a * r0 * a⁻¹ := by rw [← hzcomm.eq]; group
      _ = s0 := ha
  have hproduct : ConjClasses.mk (t * r0) = ConjClasses.mk (t * s0) := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    apply isConj_iff.mpr
    refine ⟨c, ?_⟩
    calc
      c * (t * r0) * c⁻¹ = (c * t * c⁻¹) * (c * r0 * c⁻¹) := by group
      _ = t * s0 := by rw [hct, hcr0]
  calc
    f (ConjClasses.mk (x * y)) = f (ConjClasses.mk (t * r)) := by rw [hxy]
    _ = f (ConjClasses.mk (t * r0)) := hfr
    _ = f (ConjClasses.mk (t * s0)) := by rw [hproduct]
    _ = f (ConjClasses.mk (t * s)) := hfs.symm

end Glauberman.ZStar.Constancy
