module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Reduction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Parity

/-!
# Coverage and a faithful pair for the noncentral J₂ centralizer

Apply the existing partner classification to (a,b^g) for g centralizing a.
The b-inverse branch would make the checked outer automorphism inner, contrary
to its parity. In the other branch, equality on the generating pair and
faithfulness of conjugation identify g with one of the 240 existing words.
Among these words only the identity fixes both points 0 and 1. Thus equality
on this pair suffices to prove equality of arbitrary centralizer elements.

Source: Aschbacher–Smith 16.1.5(8), printed p.1172, and the retained ATLAS
J2G1-p100B0 standard-pair and parity certificates.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2Inner

open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate
open Sporadic.LeechRelated.J2.ExceptionalParabolics
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims

private theorem eq_of_pair (f g : MulAut Carrier) (ha : f a = g a) (hb : f b = g b) :
    f = g := by
  apply MulEquiv.toMonoidHom_injective
  apply MonoidHom.eq_of_eqOn_dense closure_pair_eq_top
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact ha
  · rw [Set.mem_singleton_iff] at hx
    subst x
    exact hb

theorem a_centralizer_cover (g : Carrier) (hg : g ∈ centralizer ({a} : Set Carrier)) :
    ∃ i : Fin 240, g = conjugator i := by
  have hga : MulAut.conj g a = a := by
    have hc := mem_centralizer_singleton_iff.mp hg
    change g * a * g⁻¹ = a
    rw [hc, mul_inv_cancel_right]
  have hp : PairProfile a (MulAut.conj g b) := by
    simpa only [hga] using pair_profile.map (MulAut.conj g)
  obtain ⟨j, hj⟩ := normalForm_cover (MulAut.conj g b)
  have h := (pairProfile_iff_ambient _).mp hp
  rw [hj] at h
  obtain ⟨i, inv, hi⟩ := normalForm_classification j h
  have hb : MulAut.conj g b = partner i inv := by
    apply Sporadic.LeechRelated.J2.inclusion_injective
    rw [hj, hi, partner_inclusion]
  cases inv with
  | false =>
    refine ⟨i, J2Reduction.conj_injective ?_⟩
    exact eq_of_pair _ _ (hga.trans (conjugator_centralizes i).symm) hb
  | true =>
    have he : MulAut.conj g = MulAut.conj (conjugator i) * involutionAut :=
      eq_of_pair _ _ (by simpa only [MulAut.mul_apply, involutionAut_a,
        conjugator_centralizes] using hga) (by simpa only [MulAut.mul_apply,
          involutionAut_b, partner, Bool.true_eq, ↓reduceIte] using hb)
    have hinner : MulAut.conj ((conjugator i)⁻¹ * g) = involutionAut := by
      rw [map_mul, map_inv, he, inv_mul_cancel_left]
    exact (involutionAut_not_inner ⟨_, hinner⟩).elim

set_option maxRecDepth 100000 in
private theorem word_point_kernel : ∀ i,
    conjugatorTable i 0 = 0 → conjugatorTable i 1 = 1 → i = 0 := by
  apply allFin
  decide +kernel

private theorem centralizer_eq_one_of_fix
    (x : Subgroup.centralizer ({a} : Set Carrier))
    (h0 : inclusion x.val 0 = 0) (h1 : inclusion x.val 1 = 1) : x = 1 := by
  obtain ⟨i, hi⟩ := a_centralizer_cover x.val x.property
  rw [hi, conjugator_inclusion] at h0 h1
  have hz := word_point_kernel i h0 h1
  apply Subtype.ext
  rw [hi, hz]
  rfl

/-- The action of C(a) on the ordered pair of points (0,1) is faithful. -/
theorem a_centralizer_ext {x y : Subgroup.centralizer ({a} : Set Carrier)}
    (h0 : inclusion x.val 0 = inclusion y.val 0)
    (h1 : inclusion x.val 1 = inclusion y.val 1) : x = y := by
  have h : y⁻¹ * x = 1 := by
    apply centralizer_eq_one_of_fix
    · change inclusion (y.val⁻¹ * x.val) 0 = 0
      rw [map_mul, map_inv, Equiv.Perm.mul_apply, h0]
      exact (inclusion y.val).symm_apply_apply 0
    · change inclusion (y.val⁻¹ * x.val) 1 = 1
      rw [map_mul, map_inv, Equiv.Perm.mul_apply, h1]
      exact (inclusion y.val).symm_apply_apply 1
  exact (inv_mul_eq_one.mp h).symm
end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2Inner
