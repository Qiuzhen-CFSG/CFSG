module
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.GroupTheory.PGroup.SmallFrattiniLinearForms
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Binary orbit spans of literal conjugate closures

A surjective binary quotient of U=⟨V^H⟩ is spanned by the H-orbit of the
single nonzero image of V. The proof lifts the span to a subgroup of U and
checks the actual conjugate generators. The Frattini specialization retains
the original automorphism action and quotient map.

This is the orbit-span step used in the selected Chapter 14 normal Bender
and index-five arguments, Aschbacher–Smith 14.2.16 and 14.2.20, pp.985–987.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Representation
variable {G E : Type*} [Group G] [Group E] [IsElementaryAbelian 2 E]

/-- A binary quotient of a literal conjugate span is spanned by the orbit
of the nonzero image of its seed line. -/
theorem conjugateSpan_binary_orbit_span
    (V H U : Subgroup G) (hVU : V ≤ U) (hU : U = conjugateSpanBy V H)
    (c : U →* E) (hc : Function.Surjective c) (actor : H →* MulAut E)
    (hequiv : ∀ h : H, ∀ x : U, ∀ hx,
      c ⟨h.val*x.val*h.val⁻¹,hx⟩ = actor h (c x))
    (w : E) (hseed : ∀ v : V, c (inclusion hVU v) = 1 ∨ c (inclusion hVU v) = w) :
    Submodule.span (ZMod 2)
      (Set.range (fun h : H => elementaryRepresentation (p := 2) actor h (Additive.ofMul w))) = ⊤ := by
  let S := Submodule.span (ZMod 2)
    (Set.range (fun h : H => elementaryRepresentation (p := 2) actor h (Additive.ofMul w)))
  let P : Subgroup E := S.toAddSubgroup.toSubgroup'
  have hHU : H ≤ normalizer (U : Set G) := hU ▸ le_normalizer_conjugateSpanBy V H
  have hUP : U ≤ ((P.comap c).map U.subtype) := by
    conv_lhs => rw [hU]
    apply (closure_le _).mpr
    rintro _ ⟨h,hh,v,hv,rfl⟩
    have hx : h*v*h⁻¹ ∈ U := le_normalizer_iff.mp hHU h hh v (hVU hv)
    refine mem_map.mpr ⟨⟨h*v*h⁻¹,hx⟩,?_,rfl⟩
    change Additive.ofMul (c ⟨h*v*h⁻¹,hx⟩) ∈ S
    have hmove := hequiv ⟨h,hh⟩ (inclusion hVU ⟨v,hv⟩) hx
    simp only [coe_inclusion] at hmove
    rw [hmove]
    rcases hseed ⟨v,hv⟩ with hz | hw
    · rw [hz,map_one]
      exact S.zero_mem
    · rw [hw]
      exact Submodule.subset_span ⟨⟨h,hh⟩,rfl⟩
  apply top_unique
  intro x _
  obtain ⟨u,hu⟩ := hc x.toMul
  obtain ⟨y,hy,he⟩ := hUP u.property
  have hyu : y = u := Subtype.ext he
  subst y
  change Additive.ofMul (c u) ∈ S at hy
  simpa only [hu,ofMul_toMul] using hy

variable [Finite G]
/-- The same statement on the original Frattini quotient and its actual
induced automorphism homomorphism. This is the quotient used in both
selected Chapter 14 orbit arguments. -/
theorem conjugateSpan_frattini_orbit_span
    (V H U : Subgroup G) (hVU : V ≤ U) (hU : U = conjugateSpanBy V H)
    (htwo : IsPGroup 2 U) (actor : H →* MulAut U)
    (hactor : ∀ h : H, ∀ x : U, (actor h x : G) = h.val*x.val*h.val⁻¹)
    (w : U ⧸ frattini U)
    (hseed : ∀ v : V, QuotientGroup.mk' (frattini U) (inclusion hVU v) = 1 ∨
      QuotientGroup.mk' (frattini U) (inclusion hVU v) = w) :
    letI : IsElementaryAbelian 2 (U ⧸ frattini U) := SmallFrattini.quotientElementary htwo
    Submodule.span (ZMod 2) (Set.range (fun h : H => elementaryRepresentation (p := 2)
      ((quotientAut (frattini U)).comp actor) h (Additive.ofMul w))) = ⊤ := by
  let : IsElementaryAbelian 2 (U ⧸ frattini U) := SmallFrattini.quotientElementary htwo
  apply conjugateSpan_binary_orbit_span V H U hVU hU
    (QuotientGroup.mk' (frattini U)) (QuotientGroup.mk'_surjective _)
    ((quotientAut (frattini U)).comp actor) ?_ w hseed
  intro h x hx
  change QuotientGroup.mk' (frattini U) _ = quotientAut (frattini U) (actor h)
    (QuotientGroup.mk' (frattini U) x)
  rw [quotientAut_apply_mk]
  apply congrArg (QuotientGroup.mk' (frattini U))
  exact Subtype.ext (hactor h x).symm
end Representation
