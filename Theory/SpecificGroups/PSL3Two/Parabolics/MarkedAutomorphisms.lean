module

public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Coverage
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.SymmetricModels

/-!
# Automorphisms preserving a binary parabolic residual

An arbitrary automorphism preserving O²(P), for either standard parabolic P,
is conjugation by an element of P. Fixing the actual quotient O²(P)/O₂(O²(P))
puts the implementer in O²(P); two-power order puts it in its two-core.
The equality of automorphisms is retained, so an ambient actor can be adjusted
by a lift of this implementer. No innerness premise is imposed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.21(1), printed p.957, covered-A₆ paragraph. Pointwise fixation of the
cubic quotient is deliberately distinct from fixation of the whole component.
-/

public section
namespace Matrix.PSL3Two.MarkedAutomorphisms
open Subgroup

/-- Pointwise fixation of the actual core quotient is equivalent to the
ambient displacement lying in the embedded intrinsic core. -/
theorem quotient_fixed_iff {G : Type*} [Group G] (A : Subgroup G) (α : MulAut G)
    (hm : ∀ a ∈ A, α a ∈ A) :
    (∀ a : A, ((⟨α a, hm a a.property⟩ : A) : A ⧸ pCore 2 A) =
      (a : A ⧸ pCore 2 A)) ↔
      ∀ a ∈ A, α a * a⁻¹ ∈ A.pCoreIn 2 := by
  constructor
  · intro h a ha
    have hh := QuotientGroup.eq_iff_div_mem.mp (h ⟨a, ha⟩)
    simpa only [pCoreIn, div_eq_mul_inv, map_mul, map_inv, Subgroup.subtype_apply] using
      mem_map_of_mem A.subtype hh
  · intro h a
    apply QuotientGroup.eq_iff_div_mem.mpr
    obtain ⟨x, hx, he⟩ := h a a.property
    have heq : x = (⟨α a, hm a a.property⟩ : A) / a :=
      Subtype.ext (by
        simpa only [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.subtype_apply] using he)
    exact heq ▸ hx

/-- Preserving either intrinsic residual excludes diagram action. -/
theorem preserving_residual_is_conj (P : Subgroup SL)
    (hP : P = pointParabolicSL ∨ P = lineParabolicSL) (α : MulAut SL)
    (hA : (residual P).map α.toMonoidHom = residual P) :
    ∃ g ∈ P, α = MulAut.conj g := by
  have hm (a : SL) (ha : a ∈ residual P) : α a ∈ residual P := by
    rw [← hA]
    exact mem_map_of_mem α.toMonoidHom ha
  rcases hP with rfl | rfl
  · rw [point_residual] at hm
    exact point_implementer α hm
  · rw [line_residual] at hm
    exact line_implementer α hm

private theorem point_quotient_implementer (α : MulAut SL)
    (hA : ∀ a ∈ pointA, α a ∈ pointA)
    (hQ : ∀ a ∈ pointA, α a * a⁻¹ ∈ pointA.pCoreIn 2) :
    ∃ g ∈ pointA, α = MulAut.conj g := by
  obtain ⟨g, hg, he⟩ := point_implementer α hA
  refine ⟨g, quotient_fixer_test g hg ?_, he⟩
  have hh := hQ cubic cubic_mem
  rwa [he, MulAut.conj_apply, point_core] at hh

private theorem line_quotient_implementer (α : MulAut SL)
    (hA : ∀ a ∈ lineA, α a ∈ lineA)
    (hQ : ∀ a ∈ lineA, α a * a⁻¹ ∈ lineA.pCoreIn 2) :
    ∃ g ∈ lineA, α = MulAut.conj g := by
  have hm (a : SL) (ha : a ∈ pointA) : diagram a ∈ lineA := by
    rw [← pointA_map_diagram]
    exact mem_map_of_mem diagram.toMonoidHom ha
  have hline : ∀ a ∈ lineA, α a * a⁻¹ ∈ lineV := by
    simpa only [line_core] using hQ
  have hq := involutive_displacement_transport pointA pointV diagram α
    diagram_involutive hline
  obtain ⟨g, hg, he⟩ := point_quotient_implementer (diagram * α * diagram)
    (line_preserving_transport α hA) (by simpa only [point_core] using hq)
  exact ⟨diagram g, hm g hg, diagram_conj_transport α g he⟩

/-- Pointwise fixation of the quotient by the intrinsic two-core refines the
implementer to the residual. The premise only asks for quotient fixation. -/
theorem quotient_fixer_is_conj (P : Subgroup SL)
    (hP : P = pointParabolicSL ∨ P = lineParabolicSL) (α : MulAut SL)
    (hA : (residual P).map α.toMonoidHom = residual P)
    (hQ : ∀ a ∈ residual P, α a * a⁻¹ ∈ (residual P).pCoreIn 2) :
    ∃ g ∈ residual P, α = MulAut.conj g := by
  have hm (a : SL) (ha : a ∈ residual P) : α a ∈ residual P := by
    rw [← hA]
    exact mem_map_of_mem α.toMonoidHom ha
  rcases hP with rfl | rfl
  · rw [point_residual] at hm hQ ⊢
    exact point_quotient_implementer α hm hQ
  · rw [line_residual] at hm hQ ⊢
    exact line_quotient_implementer α hm hQ

/-- The implementer of a quotient-fixing automorphism of two-power order lies
in the actual embedded two-core. -/
theorem two_quotient_fixer_is_conj (P : Subgroup SL)
    (hP : P = pointParabolicSL ∨ P = lineParabolicSL) (α : MulAut SL)
    (hA : (residual P).map α.toMonoidHom = residual P)
    (hQ : ∀ a ∈ residual P, α a * a⁻¹ ∈ (residual P).pCoreIn 2)
    (hTwo : ∃ n : ℕ, α ^ (2 ^ n) = 1) :
    ∃ g ∈ (residual P).pCoreIn 2, α = MulAut.conj g := by
  obtain ⟨g, hg, he⟩ := quotient_fixer_is_conj P hP α hA hQ
  have hpow : ∃ n : ℕ, g ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := hTwo
    refine ⟨n, conj_injective ?_⟩
    rw [map_pow, ← he, hn, map_one]
  refine ⟨g, ?_, he⟩
  rcases hP with rfl | rfl
  · rw [point_residual, point_core]
    rw [point_residual] at hg
    exact point_two_element g hg hpow
  · rw [line_residual, line_core]
    rw [line_residual] at hg
    change diagram g ∈ pointV
    apply point_two_element (diagram g) hg
    obtain ⟨n, hn⟩ := hpow
    exact ⟨n, by rw [← map_pow, hn, map_one]⟩

end Matrix.PSL3Two.MarkedAutomorphisms
