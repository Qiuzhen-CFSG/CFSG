module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.SmallSymplectic
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InnerAction

/-!
# The genuine triple-cover branch of the source core module

The alternating polar form on the original Q/Z(Q) excludes a simple M₂₂
cover, even if its action were reducible. The previously constructed perfect
cover is therefore the native triple cover. Its order shows that it is the
entire inverse image of the inner Mathieu automorphisms. James uniqueness
identifies its core action, and the actual cubic Sylow has C_Q(X) = Z(Q).

These are the module and fixed-core steps of Aschbacher–Segev, *The uniqueness
of groups of type J₄*, Invent. Math. 105 (1991), (4.1), printed p.597,
DOI 10.1007/BF01232280. The centralizer in H/⟨z⟩ is constructed separately
in `SourceRecognition.CubicCentralizer`; ambient recognition still requires
the later local geometry, comparison and cycle-base arguments.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Subgroup LocalGeometry Sporadic.Mathieu Representation
variable {G : Type*} [Group G] [Finite G] {z : G} (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))
include h

/-- The source orthogonal action rules out the simple-cover alternative. -/
theorem innerDerived_not_simple :
    ¬ Nonempty ((_root_.commutator (innerPreimage e)) ≃* M22) := by
  rintro ⟨ec⟩
  let := h.extraspecial
  let ρ := (innerDerivedRepresentation h e).comp ec.symm.toMonoidHom
  apply m22_not_symplectic_of_degree_le_twelve ρ
    ((innerDerivedRepresentation_injective h e).comp ec.symm.injective)
    (coreSpace_finrank h).le (coreQuadraticForm (z := z)).polarBilin
    coreQuadraticForm_polar_alt coreQuadraticForm_nondegenerate
  intro g v w
  exact coreQuadraticForm_polar_invariant h (innerDerivedInclusion e (ec.symm g)) v w

/-- The original perfect cover is the genuine native triple cover. -/
theorem innerDerived_is_triple :
    Nonempty ((_root_.commutator (innerPreimage e)) ≃* M22TripleCover) :=
  (innerDerived_simple_or_triple e).resolve_left (innerDerived_not_simple h e)

/-- No extra central factor remains outside the constructed perfect cover. -/
theorem innerPreimage_derived_eq_top : _root_.commutator (innerPreimage e) = ⊤ := by
  obtain ⟨ec⟩ := innerDerived_is_triple h e
  have hd : Nat.card (_root_.commutator (innerPreimage e)) = 1330560 :=
    (Nat.card_congr ec.toEquiv).trans M22TripleCover.card
  have hc := (innerProjection e).ker.card_mul_index
  rw [innerProjection_kernel_card, index_ker,
    MonoidHom.range_eq_top.mpr (innerProjection_surjective e), card_top, m22_order] at hc
  apply eq_of_le_of_card_ge le_top
  rw [card_top, hd, ← hc]

/-- A marking of the full inner inverse image, retaining its original carrier. -/
noncomputable def innerPreimageTripleEquiv : innerPreimage e ≃* M22TripleCover :=
  ((MulEquiv.subgroupCongr (innerPreimage_derived_eq_top h e)).trans topEquiv).symm.trans
    (innerDerived_is_triple h e).some

/-- The fixed-core clause of AS91 (4.1) for the original embedded cubic Sylow. -/
theorem core_cubic_centralizer (X : Sylow 3 (CubicLift.subgroup e)) :
    (Subgroup.centralizer (cubicSylowImage e X : Set (centralizer z))).subgroupOf (core z) =
      center (core z) :=
  core_cubic_centralizer_of_triple h e (innerDerived_is_triple h e).some X

/-- The cubic Sylow acts without nonidentity fixed points on Q/Z(Q). -/
theorem cubicAction_fixed_iff (X : Sylow 3 (CubicLift.subgroup e))
    (v : core z ⧸ center (core z)) :
    (∀ x : X, cubicAction h e X x v = v) ↔ v = 1 :=
  cubicAction_fixed_iff_of_triple h e (innerDerived_is_triple h e).some X v

/-- The source hypotheses construct a faithful irreducible James action on
the literal core quotient, together with its original cubic centralizer. -/
theorem source_module :
    letI := h.extraspecial
    ∃ (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))
      (ec : (_root_.commutator (innerPreimage e)) ≃* M22TripleCover),
      Function.Injective (innerDerivedRepresentation h e) ∧
      Module.finrank (ZMod 2) (CoreSpace (z := z)) = 12 ∧
      (coreQuadraticForm (z := z)).polarBilin.Nondegenerate ∧
      (coreQuadraticForm (z := z)).polarBilin.IsAlt ∧
      (∀ x v, coreQuadraticForm (innerDerivedRepresentation h e x v) = coreQuadraticForm v) ∧
      (innerDerivedRepresentation h e).IsIrreducible ∧
      Nonempty (Representation.Equiv (innerDerivedRepresentation h e)
        (M22TripleCover.representationOfEquiv ec)) ∧
      ∀ X : Sylow 3 (CubicLift.subgroup e),
        (Subgroup.centralizer (cubicSylowImage e X : Set (centralizer z))).subgroupOf (core z) =
          center (core z) := by
  let := h.extraspecial
  obtain ⟨e⟩ := h.cubic_quotient
  obtain ⟨ec⟩ := innerDerived_is_triple h e
  exact ⟨e, ec, innerDerivedRepresentation_injective h e, coreSpace_finrank h,
    coreQuadraticForm_nondegenerate, coreQuadraticForm_polar_alt,
    innerDerivedRepresentation_preserves h e, (innerDerivedRepresentation_of_triple h e ec).1,
    (innerDerivedRepresentation_of_triple h e ec).2, core_cubic_centralizer h e⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
