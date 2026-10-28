module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CoreOrbits
public import Theory.Representation.Mathieu.M22James.Ambient

/-!
# The full cubic action and distinct core involution classes

The native module marking extends from the inner triple cover to all of H/Q:
its faithful action normalizes that cover, hence lies in the native matrix
extension. Surjectivity of the original cubic projection rules out the inner
image, giving an actual isomorphism with the full native extension. The outer
generator preserves the four vector-orbit labels, as checked on their roots;
normality propagates those checks to every vector. Thus native labels classify
actual H-conjugacy in the noncentral core, proving that the two involutions
constructed earlier represent different classes.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*, Invent.
Math. 105 (1991), the orbit clause of (4.2), printed p.597,
DOI 10.1007/BF01232280. Stabilizer structures and subsequent fusion remain
separate obligations; this is not the ambient recognition theorem.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Subgroup Sporadic.Mathieu Representation
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open M22TripleCover.Ambient

namespace VectorOrbits

theorem binaryAction_cover (g : M22TripleCover) (v : M22TripleCover.BinarySpace) :
    binaryAction (coverInclusion g) v = M22TripleCover.binaryRepresentation g v := rfl

private theorem outer_label_root (n : Word)
    (hn : n = 0 ∨ n = 1 ∨ n = 4 ∨ n = 7) :
    label (binaryAction outerElement (decode n)) = label (decode n) := by
  rcases hn with rfl | rfl | rfl | rfl
  · have he : binaryAction outerElement (decode 0) = decode 0 := by decide +kernel
    rw [he]
  · have he : binaryAction outerElement (decode 1) = decode 2054 := by decide +kernel
    rw [he, label_decode, label_decode]
    decide +kernel
  · have he : binaryAction outerElement (decode 4) = decode 2052 := by decide +kernel
    rw [he, label_decode, label_decode]
    decide +kernel
  · have he : binaryAction outerElement (decode 7) = decode 7 := by decide +kernel
    rw [he]

theorem outer_label (v : M22TripleCover.BinarySpace) :
    label (binaryAction outerElement v) = label v := by
  obtain ⟨n,rfl⟩ := decode_bijective.surjective v
  obtain ⟨g,hg⟩ := orbit_transport n
  have hc : outerElement * coverInclusion g * outerElement⁻¹ ∈ coverSubgroup :=
    Subgroup.Normal.conj_mem inferInstance _ (by rw [← coverInclusion_range]; exact ⟨g,rfl⟩) _
  obtain ⟨d,hd⟩ := (show outerElement * coverInclusion g * outerElement⁻¹ ∈ coverInclusion.range by
    rwa [coverInclusion_range])
  have he : outerElement * coverInclusion g = coverInclusion d * outerElement := by
    rw [hd]
    group
  rw [← hg, ← binaryAction_cover, ← Module.End.mul_apply, ← map_mul, he, map_mul,
    Module.End.mul_apply, binaryAction_cover, label_invariant, outer_label_root _ (root_cases n),
    binaryAction_cover, label_invariant]

theorem ambient_label_invariant (g : actionGroup) (v : M22TripleCover.BinarySpace) :
    label (binaryAction g v) = label v := by
  by_cases hg : g ∈ coverSubgroup
  · obtain ⟨d,rfl⟩ := (show g ∈ coverInclusion.range by rwa [coverInclusion_range])
    exact label_invariant d v
  · have hm : g * outerElement ∈ coverSubgroup :=
      (Subgroup.mul_mem_iff_of_index_two coverSubgroup_index).mpr
        (iff_of_false hg outerElement_not_mem_cover)
    obtain ⟨d,hd⟩ := (show g * outerElement ∈ coverInclusion.range by rwa [coverInclusion_range])
    have he : g = coverInclusion d * outerElement := by
      rw [hd, mul_assoc, ← pow_two, outerElement_sq, mul_one]
    rw [he, map_mul, Module.End.mul_apply, binaryAction_cover, label_invariant, outer_label]

end VectorOrbits

variable {G : Type*} [Group G] [Finite G] {z : G} (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))
variable (X : Sylow 3 (LocalGeometry.CubicLift.subgroup e))
variable [IsExtraspecial 2 (core z)]

theorem coreNativeEquiv_inner (g : innerPreimage e) (v : CoreSpace (z := z)) :
    coreNativeEquiv h e X (coreBinaryRepresentation h g v) =
      M22TripleCover.binaryRepresentation (innerPreimageTripleEquiv h e g) (coreNativeEquiv h e X v) := by
  obtain ⟨c,rfl⟩ := (cubicCentralizerEquiv h e X).surjective g
  exact coreNativeEquiv_intertwines h e X c v

noncomputable def coreNativeInnerEquiv :
    Representation.Equiv ((coreBinaryRepresentation h).comp (innerPreimage e).subtype)
      (M22TripleCover.representationOfEquiv (innerPreimageTripleEquiv h e)) :=
  Representation.Equiv.mk (coreNativeEquiv h e X) (fun g => by
    apply LinearMap.ext
    intro v
    exact coreNativeEquiv_inner h e X g v)

noncomputable def coreAmbientHom : (centralizer z ⧸ core z) →* actionGroup :=
  markedTripleAmbientHom (coreBinaryRepresentation h) (innerPreimage e)
    (innerPreimageTripleEquiv h e) (coreNativeInnerEquiv h e X)

theorem coreAmbientHom_intertwines (g : centralizer z ⧸ core z) (v : CoreSpace (z := z)) :
    coreNativeEquiv h e X (coreBinaryRepresentation h g v) =
      binaryAction (coreAmbientHom h e X g) (coreNativeEquiv h e X v) :=
  markedTripleAmbientHom_intertwining (coreBinaryRepresentation h) (innerPreimage e)
    (innerPreimageTripleEquiv h e) (coreNativeInnerEquiv h e X) g v

theorem core_label_invariant (g : centralizer z ⧸ core z) (v : CoreSpace (z := z)) :
    VectorOrbits.label (coreNativeEquiv h e X (coreBinaryRepresentation h g v)) =
      VectorOrbits.label (coreNativeEquiv h e X v) := by
  rw [coreAmbientHom_intertwines, VectorOrbits.ambient_label_invariant]

theorem coreAmbientHom_injective : Function.Injective (coreAmbientHom h e X) :=
  markedTripleAmbientHom_injective _ _ _ _ (coreBinaryRepresentation_injective h)

theorem coreAmbientHom_surjective : Function.Surjective (coreAmbientHom h e X) := by
  apply MonoidHom.range_eq_top.mp
  rcases markedTripleAmbientHom_range_cases (coreBinaryRepresentation h) (innerPreimage e)
      (innerPreimageTripleEquiv h e) (coreNativeInnerEquiv h e X) with hc | ht
  · obtain ⟨g,hg⟩ := e.surjective (m22DesignAutToAut m22OuterDesignAut)
    have hm : coreAmbientHom h e X g ∈ coverSubgroup := hc ▸ (show coreAmbientHom h e X g ∈ (coreAmbientHom h e X).range from ⟨g,rfl⟩)
    have hi := (markedTripleAmbientHom_mem_cover_iff (coreBinaryRepresentation h) (innerPreimage e)
      (innerPreimageTripleEquiv h e) (coreNativeInnerEquiv h e X)
      (coreBinaryRepresentation_injective h) g).mp hm
    change e.projection g ∈ m22InnerAut at hi
    rw [hg] at hi
    exact False.elim (m22OuterAutomorphism_not_mem_inner hi)
  · exact ht

/-- The full source action is the genuine native cubic extension. -/
noncomputable def coreAmbientEquiv : (centralizer z ⧸ core z) ≃* actionGroup :=
  MulEquiv.ofBijective (coreAmbientHom h e X)
    ⟨coreAmbientHom_injective h e X, coreAmbientHom_surjective h e X⟩

theorem core_label_of_isConj (a b : core z)
    (hab : IsConj (a : centralizer z) (b : centralizer z)) :
    VectorOrbits.label (coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) a))) =
    VectorOrbits.label (coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) b))) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hab
  have he : MulAut.conjNormal g a = b := Subtype.ext hg
  have hv : coreBinaryRepresentation h (QuotientGroup.mk' (core z) g)
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) a)) =
      Additive.ofMul (QuotientGroup.mk' (center (core z)) b) := by
    change Additive.ofMul (coreQuotientAction h (QuotientGroup.mk' (core z) g)
      (QuotientGroup.mk' (center (core z)) a)) = _
    rw [coreQuotientAction_mk, he]
  exact (core_label_invariant h e X (QuotientGroup.mk' (core z) g) _).symm.trans
    (congrArg (fun v => VectorOrbits.label (coreNativeEquiv h e X v)) hv)

/-- Native labels classify actual H-conjugacy in the noncentral core. -/
theorem core_isConj_iff_label (a b : core z) (ha : a ∉ center (core z)) :
    IsConj (a : centralizer z) (b : centralizer z) ↔
      VectorOrbits.label (coreNativeEquiv h e X
        (Additive.ofMul (QuotientGroup.mk' (center (core z)) a))) =
      VectorOrbits.label (coreNativeEquiv h e X
        (Additive.ofMul (QuotientGroup.mk' (center (core z)) b))) :=
  ⟨core_label_of_isConj h e X a b, core_isConj_of_label h e X a b ha⟩

omit [IsExtraspecial 2 (core z)] in
include h in
/-- These are exactly two distinct H-classes of noncentral core involutions. -/
theorem source_involution_classes :
    ∃ r₁ r₂ : core z,
      orderOf r₁ = 2 ∧ orderOf r₂ = 2 ∧
      r₁ ∉ center (core z) ∧ r₂ ∉ center (core z) ∧
      ¬ IsConj (r₁ : centralizer z) (r₂ : centralizer z) ∧
      ∀ r : core z, orderOf r = 2 → r ∉ center (core z) →
        IsConj (r : centralizer z) (r₁ : centralizer z) ∨
          IsConj (r : centralizer z) (r₂ : centralizer z) := by
  let := h.extraspecial
  obtain ⟨e⟩ := h.cubic_quotient
  obtain ⟨X⟩ := (inferInstance : Nonempty (Sylow 3 (LocalGeometry.CubicLift.subgroup e)))
  obtain ⟨r₁,r₂,h₁,h₂,h₁c,h₂c,e₁,e₂,hcov⟩ := source_involution_orbit_cover h e X
  refine ⟨r₁,r₂,h₁,h₂,h₁c,h₂c,?_,hcov⟩
  intro hc
  have he := core_label_of_isConj h e X r₁ r₂ hc
  rw [e₁,e₂,VectorOrbits.label_decode,VectorOrbits.label_decode] at he
  exact (by decide : (VectorOrbits.treeRow 4).root ≠ (VectorOrbits.treeRow 7).root) he

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
