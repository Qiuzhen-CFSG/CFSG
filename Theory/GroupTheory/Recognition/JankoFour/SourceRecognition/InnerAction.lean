module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InnerCover
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.OrthogonalAction
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.TripleModule

/-!
# The source core action of the constructed Mathieu cover

The perfect cover constructed inside H/Q acts faithfully on the literal
Q/Z(Q), preserving its quadratic form. In the triple-cover case the
minimum-degree argument proves irreducibility, and James uniqueness
identifies this action with the native module. The same identification
makes the original cubic kernel fixed-point-free on Q/Z(Q), and gives
C_Q(X) = Z(Q) for the source Sylow cubic X, with its actual embedding in H.

The final theorem retains the simple-cover alternative. Excluding that
alternative is necessary before this is the full module claim of (4.1).
Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*, Invent.
Math. 105 (1991), (4.1), printed p.597, DOI 10.1007/BF01232280.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Subgroup LocalGeometry Sporadic.Mathieu Representation
variable {G : Type*} [Group G] [Finite G] {z : G} (h : IsTypeJ4 z)
variable [IsExtraspecial 2 (core z)]
variable (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))

/-- The constructed perfect cover acts through its actual inclusion into H/Q. -/
noncomputable def innerDerivedRepresentation :
    Representation (ZMod 2) (_root_.commutator (innerPreimage e)) (CoreSpace (z := z)) :=
  (coreBinaryRepresentation h).comp (innerDerivedInclusion e)

theorem innerDerivedRepresentation_injective :
    Function.Injective (innerDerivedRepresentation h e) :=
  (coreBinaryRepresentation_injective h).comp (innerDerivedInclusion_injective e)

theorem innerDerivedRepresentation_preserves (x : _root_.commutator (innerPreimage e))
    (v : CoreSpace (z := z)) :
    coreQuadraticForm (innerDerivedRepresentation h e x v) = coreQuadraticForm v :=
  coreQuadraticForm_invariant h _ v

/-- A triple-cover marking identifies the entire original core module. -/
theorem innerDerivedRepresentation_of_triple
    (ec : (_root_.commutator (innerPreimage e)) ≃* M22TripleCover) :
    (innerDerivedRepresentation h e).IsIrreducible ∧
      Nonempty (Representation.Equiv (innerDerivedRepresentation h e)
        (M22TripleCover.representationOfEquiv ec)) :=
  tripleCover_equiv_of_degree_le_twelve ec _ (innerDerivedRepresentation_injective h e)
    (coreSpace_finrank h).le

/-- The source action yields an actual simple-cover alternative or a complete
identification of its restriction with the native James module. -/
theorem innerDerived_simple_or_james :
    Nonempty ((_root_.commutator (innerPreimage e)) ≃* M22) ∨
      ∃ ec : (_root_.commutator (innerPreimage e)) ≃* M22TripleCover,
        (innerDerivedRepresentation h e).IsIrreducible ∧
          Nonempty (Representation.Equiv (innerDerivedRepresentation h e)
            (M22TripleCover.representationOfEquiv ec)) := by
  rcases innerDerived_simple_or_triple e with hs | ht
  · exact Or.inl hs
  · obtain ⟨ec⟩ := ht
    exact Or.inr ⟨ec, innerDerivedRepresentation_of_triple h e ec⟩

/-- In the triple case the original cubic kernel has no nonzero common fixed vector. -/
theorem cubicKernel_fixed_eq_zero_of_triple
    (ec : (_root_.commutator (innerPreimage e)) ≃* M22TripleCover)
    (v : CoreSpace (z := z))
    (hv : ∀ x : e.projection.ker, coreBinaryRepresentation h x v = v) : v = 0 := by
  let := (innerDerivedRepresentation_of_triple h e ec).1
  let a := ec.symm M22TripleCover.scalar
  have ha : a ∈ center (_root_.commutator (innerPreimage e)) :=
    M22TripleCover.scalar_mem_center_of_equiv ec
  have hk : innerDerivedInclusion e a ∈ e.projection.ker := by
    change e.projection (innerDerivedInclusion e a) = 1
    rw [innerDerivedInclusion_projection]
    have he : (innerDerivedCover e).toMonoidHom a = 1 :=
      show a ∈ (innerDerivedCover e).toMonoidHom.ker from (innerDerived_kernel_eq_center e).symm ▸ ha
    rw [he, map_one]
  exact (M22TripleCover.scalar_fixed_iff_of_equiv ec (innerDerivedRepresentation h e)
    (innerDerivedRepresentation_injective h e) v).mp (hv ⟨innerDerivedInclusion e a, hk⟩)

omit [IsExtraspecial 2 (core z)] in
/-- In the triple case the chosen source Sylow cubic fixes exactly the identity
of the actual central quotient. -/
theorem cubicAction_fixed_iff_of_triple
    (ec : (_root_.commutator (innerPreimage e)) ≃* M22TripleCover)
    (X : Sylow 3 (CubicLift.subgroup e)) (v : core z ⧸ center (core z)) :
    (∀ x : X, cubicAction h e X x v = v) ↔ v = 1 := by
  let := h.extraspecial
  constructor
  · intro hv
    have he := cubicKernel_fixed_eq_zero_of_triple h e ec (Additive.ofMul v) (by
      intro x
      obtain ⟨y,rfl⟩ := (cubicKernelEquiv e h X).surjective x
      exact congrArg Additive.ofMul (hv y))
    exact congrArg Additive.toMul he
  · rintro rfl x
    exact map_one _

omit [IsExtraspecial 2 (core z)] in
include h in
/-- The center of Q is the full center of H under the literal inclusion. -/
theorem core_center_eq_centralizer_center :
    (center (core z)).map (core z).subtype = center (centralizer z) := by
  apply map_injective (centralizer z).subtype_injective
  exact (core_center_image h).trans h.centralizer_center_image.symm

omit [IsExtraspecial 2 (core z)] in
include h in
/-- The fixed-core clause of AS91 (4.1) in the triple-cover branch, retaining
X, Q and the actual centralizer inside H. The remaining simple-cover case
is not silently discarded. -/
theorem core_cubic_centralizer_of_triple
    (ec : (_root_.commutator (innerPreimage e)) ≃* M22TripleCover)
    (X : Sylow 3 (CubicLift.subgroup e)) :
    (Subgroup.centralizer (cubicSylowImage e X : Set (centralizer z))).subgroupOf (core z) =
      center (core z) := by
  ext q
  constructor
  · intro hq
    apply (QuotientGroup.eq_one_iff q).mp
    apply (cubicAction_fixed_iff_of_triple h e ec X _).mp
    intro x
    change cubicAction h e X x (QuotientGroup.mk' (center (core z)) q) =
      QuotientGroup.mk' (center (core z)) q
    rw [cubicAction_mk]
    congr 1
    apply Subtype.ext
    change (x.val : centralizer z) * q.val * (x.val : centralizer z)⁻¹ = q.val
    have he := hq x.val (mem_map_of_mem (CubicLift.subgroup e).subtype x.property)
    change (x.val : centralizer z) * q.val = q.val * (x.val : centralizer z) at he
    rw [he, mul_inv_cancel_right]
  · intro hq
    have hh : (q : centralizer z) ∈ center (centralizer z) :=
      (core_center_eq_centralizer_center h) ▸ mem_map_of_mem (core z).subtype hq
    exact fun x _ => mem_center_iff.mp hh x

omit [IsExtraspecial 2 (core z)] in
/-- The source hypotheses construct the original orthogonal action and a
simple-cover or fully identified triple-cover alternative. The unresolved
simple-cover branch remains visible in the conclusion. -/
theorem source_module_alternative :
    letI := h.extraspecial
    ∃ e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z),
      Function.Injective (innerDerivedRepresentation h e) ∧
      Module.finrank (ZMod 2) (CoreSpace (z := z)) = 12 ∧
      (coreQuadraticForm (z := z)).polarBilin.Nondegenerate ∧
      (coreQuadraticForm (z := z)).polarBilin.IsAlt ∧
      (∀ x v, coreQuadraticForm (innerDerivedRepresentation h e x v) = coreQuadraticForm v) ∧
      (Nonempty ((_root_.commutator (innerPreimage e)) ≃* M22) ∨
        ∃ ec : (_root_.commutator (innerPreimage e)) ≃* M22TripleCover,
          (innerDerivedRepresentation h e).IsIrreducible ∧
          Nonempty (Representation.Equiv (innerDerivedRepresentation h e)
            (M22TripleCover.representationOfEquiv ec)) ∧
          ∀ X : Sylow 3 (CubicLift.subgroup e),
            (Subgroup.centralizer (cubicSylowImage e X : Set (centralizer z))).subgroupOf (core z) =
              center (core z)) := by
  let := h.extraspecial
  obtain ⟨e⟩ := h.cubic_quotient
  refine ⟨e, innerDerivedRepresentation_injective h e, coreSpace_finrank h,
    coreQuadraticForm_nondegenerate, coreQuadraticForm_polar_alt,
    innerDerivedRepresentation_preserves h e, ?_⟩
  rcases innerDerived_simple_or_james h e with hs | ⟨ec, hi, hm⟩
  · exact Or.inl hs
  · exact Or.inr ⟨ec, hi, hm, core_cubic_centralizer_of_triple h e ec⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
