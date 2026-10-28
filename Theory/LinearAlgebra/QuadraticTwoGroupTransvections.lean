module
public import Theory.LinearAlgebra.QuadraticRankOneDisplacement
public import Theory.LinearAlgebra.FieldFourTransvectionPairs
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Rank-one quadratic isometries in a two-group

Two rank-one isometries in characteristic two fix each other's full
displacement spaces when their product has two-power order. The product
minus the identity is nilpotent; its trace is the product of the two
cross-pairings. That product vanishes. Nondegenerate polarization and the
nonsingular displacement centers force both cross-pairings to vanish.

This is used for the normal span of the original orthogonal critical actor
in Aschbacher–Smith, proof of 14.7.32, printed p.1058, refs/quasithin.pdf.
-/

public section
set_option linter.unusedSimpArgs false
open Module
namespace QuadraticForm
variable {F V : Type*} [Field F] [CharP F 2] [AddCommGroup V]
  [Module F V] [Module.Finite F V]

omit [CharP F 2] in
private theorem transvection_fixed_center
    (q : QuadraticForm F V) (hq : q.polarBilin.SeparatingLeft)
    (f g : Module.Dual F V) (v w : V) (hf : f v = 0) (hg : g w = 0)
    (hs : ∀ x, q (LinearEquiv.transvection hf x) = q x)
    (ht : ∀ x, q (LinearEquiv.transvection hg x) = q x)
    (hf0 : f ≠ 0) (hw : w ≠ 0) (hg0 : g ≠ 0)
    (hfw : f w = 0) : g v = 0 := by
  obtain ⟨x,hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra! hh
    exact hf0 (LinearMap.ext hh)
  have hpolar : QuadraticMap.polar q v w = 0 := by
    have hp : QuadraticMap.polar q (LinearEquiv.transvection hf x)
        (LinearEquiv.transvection hf w) = QuadraticMap.polar q x w := by
      unfold QuadraticMap.polar
      rw [←map_add,hs,hs,hs]
    simp only [LinearEquiv.transvection.apply,LinearMap.transvection.apply,hfw,zero_smul,add_zero,
      QuadraticMap.polar_add_left,QuadraticMap.polar_smul_left,smul_eq_mul] at hp
    exact (mul_eq_zero.mp (add_eq_left.mp hp)).resolve_left hx
  have hqw : q w ≠ 0 := by
    obtain ⟨y,hy⟩ : ∃ y, g y ≠ 0 := by
      by_contra! hh
      exact hg0 (LinearMap.ext hh)
    intro hqw
    apply q.singular_not_mem_displacement hq (LinearEquiv.transvection hg) ht
      (LinearEquiv.mem_dilatransvections_iff_finrank.mp
        (LinearEquiv.transvections_subset_dilatransvections
          (LinearEquiv.mem_transvections_iff.mpr ⟨g,w,hg,rfl⟩))) w hw hqw
    refine ⟨(g y)⁻¹ • y,?_⟩
    simp [LinearEquiv.transvection.apply,LinearMap.transvection.apply,hy]
  have he := ht v
  simp only [LinearEquiv.transvection.apply,LinearMap.transvection.apply,QuadraticMap.map_add,QuadraticMap.map_smul,
    QuadraticMap.polar_smul_right,smul_eq_mul,hpolar,mul_zero,add_zero] at he
  have hz : (g v)^2 * q w = 0 := by simpa only [pow_two] using add_eq_left.mp he
  exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp ((mul_eq_zero.mp hz).resolve_right hqw)

/-- Rank-one isometries whose product has two-power order fix each other's
whole displacement spaces. -/
theorem rank_one_two_power_fixes_displacement
    (q : QuadraticForm F V) (hq : q.polarBilin.SeparatingLeft)
    (s t : V ≃ₗ[F] V)
    (hs : ∀ x, q (s x) = q x) (ht : ∀ x, q (t x) = q x)
    (hs2 : s*s = 1) (ht2 : t*t = 1)
    (hrs : finrank F (s.toLinearMap - 1).range ≤ 1)
    (hrt : finrank F (t.toLinearMap - 1).range ≤ 1)
    (hn : ∃ n : ℕ, (s*t)^(2^n) = 1) :
    ∀ z ∈ (t.toLinearMap - 1).range, s z = z := by
  by_cases hV : Subsingleton V
  · let := hV
    exact fun _ _ => Subsingleton.elim _ _
  let : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
  let : CharP (Module.End F V) 2 :=
    charP_of_injective_algebraMap (algebraMap F (Module.End F V)).injective 2
  obtain ⟨f,v,hf,rfl⟩ := LinearEquiv.mem_transvections_iff.mp
    (LinearEquiv.mem_transvections_of_square_one_rank_one s hs2 hrs)
  obtain ⟨g,w,hg,rfl⟩ := LinearEquiv.mem_transvections_iff.mp
    (LinearEquiv.mem_transvections_of_square_one_rank_one t ht2 hrt)
  by_cases hf0 : f = 0
  · subst f
    intro z hz
    simp [LinearEquiv.transvection.apply,LinearMap.transvection.apply]
  by_cases hv : v = 0
  · subst v
    intro z hz
    simp [LinearEquiv.transvection.apply,LinearMap.transvection.apply]
  by_cases hg0 : g = 0
  · subst g
    rintro z ⟨y,rfl⟩
    simp [LinearEquiv.transvection.apply,LinearMap.transvection.apply]
  by_cases hw : w = 0
  · subst w
    rintro z ⟨y,rfl⟩
    simp [LinearEquiv.transvection.apply,LinearMap.transvection.apply]
  have hcross : f w * g v = 0 := by
    obtain ⟨n,hn⟩ := hn
    let a := (LinearEquiv.transvection hf * LinearEquiv.transvection hg).toLinearMap
    have ha : a^(2^n) = 1 := by
      change (LinearEquiv.transvection hf * LinearEquiv.transvection hg).toLinearMap^(2^n) = 1
      simpa only [map_pow,map_one,LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply] using congrArg
        (LinearEquiv.automorphismGroup.toLinearMapMonoidHom : (V ≃ₗ[F] V) →* Module.End F V) hn
    have hnil : IsNilpotent (a-1) := ⟨2^n,by
      rw [sub_pow_char_pow_of_commute 2 n (Commute.one_right a),ha,one_pow,sub_self]⟩
    have htrace := (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
    have he : a-1 = f.smulRight v + g.smulRight w + (f w • g).smulRight v := by
      ext x
      simp [a,LinearEquiv.transvection.apply,LinearMap.transvection.apply]
      module
    rw [he,map_add,map_add,LinearMap.trace_smulRight,LinearMap.trace_smulRight,
      LinearMap.trace_smulRight,hf,hg,zero_add,zero_add] at htrace
    exact htrace
  have hfw : f w = 0 := by
    rcases mul_eq_zero.mp hcross with h | h
    · exact h
    · exact transvection_fixed_center q hq g f w v hg hf ht hs hg0 hv hf0 h
  rintro z ⟨x,rfl⟩
  simp [LinearEquiv.transvection.apply,LinearMap.transvection.apply,hfw]

end QuadraticForm
