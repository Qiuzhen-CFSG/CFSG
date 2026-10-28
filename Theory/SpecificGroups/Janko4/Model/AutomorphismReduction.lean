module

public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.PGroup

/-!+# Reducing the J₄ outer calculation to two generator orbits

The certified matrices `a` and `b` generate the actual binary carrier `Model`.
We separate two missing intrinsic facts: squaring an automorphism preserves the
conjugacy class of `a`, and the square of an automorphism fixing `a` sends `b`
into its orbit under the centralizer of `a`.

Given these facts, correct the square of an arbitrary automorphism by an inner
automorphism to fix `a`. Its square is inner by generation. Thus every element
of the actual outer quotient has fourth power one, so that quotient is a
two-group. At most two conjugacy classes among the automorphic images of `a`
suffice for the first fact; the classes need not be distinguished.

These are conditional reductions, not a proof of the automorphism table.
GLS3, Table 5.3i (`refs/KGroup/GLS3/Chapter5(sec3-).tex`), gives the stronger
source result Out(J₄) = 1. The two-group consequence suffices for the inspection
in Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.510.
No order, simplicity, or automorphism-table certificate is assumed to exist.
-/

@[expose] public section

namespace Janko4.OuterReduction

/-- The two certified matrix generators determine an automorphism of the model. -/
theorem aut_ext (α β : MulAut Model) (ha : α a = β a) (hb : α b = β b) :
    α = β := by
  have h : α.toMonoidHom = β.toMonoidHom := by
    apply MonoidHom.eq_of_eqOn_dense closure_a_b
    intro x hx
    rcases hx with rfl | hx
    · exact ha
    · exact Set.mem_singleton_iff.mp hx ▸ hb
  exact MulEquiv.ext (fun x => DFunLike.congr_fun h x)

/-- The first missing model fact concerns only the class of the literal generator `a`. -/
def FirstGeneratorSquareConjugacy : Prop :=
  ∀ α : MulAut Model, ∃ g : Model, (α ^ 2) a = g * a * g⁻¹

/-- The second missing fact concerns automorphisms fixing `a`. The conjugator
must centralize `a` in the actual model, not just in an ambient matrix group. -/
def FixedGeneratorSquareOrbit : Prop :=
  ∀ α : MulAut Model, α a = a →
    ∃ c : Model, c * a = a * c ∧ (α ^ 2) b = c * b * c⁻¹

/-- A two-class bound on the automorphic images suffices; no assertion that
the two classes are distinct or individually invariant is needed. -/
theorem firstGeneratorSquareConjugacy_of_two_classes (t : Model)
    (hcover : ∀ α : MulAut Model, IsConj a (α a) ∨ IsConj t (α a)) :
    FirstGeneratorSquareConjugacy := by
  intro α
  have h : IsConj a (α (α a)) := by
    by_cases hα : IsConj a (α a)
    · exact hα.trans (α.toMonoidHom.map_isConj hα)
    · have h₁ : IsConj t (α a) := (hcover α).resolve_left hα
      have h₂ : IsConj t (α.symm a) := by
        rcases hcover α.symm with h₂ | h₂
        · have h₃ : IsConj (α a) a := by
            simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using
              α.toMonoidHom.map_isConj h₂
          exact (hα h₃.symm).elim
        · exact h₂
      simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using
        α.toMonoidHom.map_isConj (h₂.symm.trans h₁)
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  exact ⟨g, hg.symm⟩

/-- Centralizer conjugacy of the second generator, together with fixation of
the first, proves innerness on the whole generated matrix group. -/
theorem square_inner_of_fixes_a (hfixed : FixedGeneratorSquareOrbit)
    (α : MulAut Model) (ha : α a = a) :
    ∃ c : Model, α ^ 2 = MulAut.conj c := by
  obtain ⟨c, hca, hcb⟩ := hfixed α ha
  refine ⟨c, aut_ext _ _ ?_ hcb⟩
  simp only [pow_two, MulAut.mul_apply, ha, MulAut.conj_apply]
  rw [hca, mul_inv_cancel_right]

/-- Two successive square reductions give exponent dividing four in the
actual quotient Aut(Model)/Inn(Model). Both model facts remain hypotheses. -/
theorem outer_pow_four_eq_one_of_generator_orbits
    (hfirst : FirstGeneratorSquareConjugacy) (hfixed : FixedGeneratorSquareOrbit)
    (x : MulAut.Outer Model) : x ^ 4 = 1 := by
  let q : MulAut Model →* MulAut.Outer Model :=
    QuotientGroup.mk' (MulAut.innerSubgroup Model)
  have hq (g : Model) : q (MulAut.conj g) = 1 := by
    exact (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup Model) x
  obtain ⟨g, hg⟩ := hfirst α
  let β : MulAut Model := MulAut.conj g⁻¹ * α ^ 2
  have hβ : β a = a := by
    simp only [β, MulAut.mul_apply, MulAut.conj_apply, hg, inv_inv]
    group
  obtain ⟨c, hc⟩ := square_inner_of_fixes_a hfixed β hβ
  have hqβ : q β = q α ^ 2 := by
    simp only [β, map_mul, map_pow, hq, one_mul]
  have hs : q β ^ 2 = 1 := by
    rw [← map_pow, hc, hq]
  change q α ^ 4 = 1
  simpa only [hqβ, ← pow_mul] using hs

/-- The two generator-orbit facts imply the two-group restriction needed by
the quasithin outer inspection, without an order or simplicity calculation. -/
theorem outer_isPGroup_two_of_generator_orbits
    (hfirst : FirstGeneratorSquareConjugacy) (hfixed : FixedGeneratorSquareOrbit) :
    IsPGroup 2 (MulAut.Outer Model) := by
  intro x
  exact ⟨2, outer_pow_four_eq_one_of_generator_orbits hfirst hfixed x⟩

end Janko4.OuterReduction
