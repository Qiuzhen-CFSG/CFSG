module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.Transvections

/-!
# Conditional H.15.2(6) for both native hexad kernels

The earlier M24 full-transvection theorem transfers through the literal pair
line quotient to native M22 and to the full setwise pair group. These endpoints
supply the actual iterated-quotient equivalence, the group isomorphism with the
additive group of W/U, the full prescribed transvection image, and compatibility
with conjugation and the induced stabilizer/kernel action. Here U is the kernel
fixed space and W is the span of its nonidentity element fixed spaces.

All quotient constructions use the canonical restricted action. The initial
lemmas identify that action, U and W with the named native representations and
spaces, avoiding costly repeated comparison of dependent quotient instances.
Only the earlier M24 action and H.14 kernel/displacement inputs remain explicit;
the chapter parent discharges them and combines the independent module and
centralizer branches. This module does not assert those other branches.

Source: Aschbacher--Smith, H.15.2(6), printed pp.398--399,
combined manuscript of 1 March 2004.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode MathieuCode.Hexad
open MathieuCode.Hexad.CocodeAction.Transvections
open Representation.BinaryOffender
noncomputable section
namespace CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad

/-- The outer action used by the transfer is the named literal cocode action. -/
theorem outer_transvection_representation :
    quotientRepresentation (MonoidHom.id m22PairStabilizer) = m22OuterCocodeRepresentation := by
  ext g v
  rfl

/-- The inner action used by the transfer is the named native M22 action. -/
theorem inner_transvection_representation :
    quotientRepresentation m22ToPairStabilizer = m22CocodeRepresentation := rfl

/-- The transfer's outer U is literally the fixed space for the native action. -/
theorem outer_transvection_fixed :
    fixed (MonoidHom.id m22PairStabilizer) (m22OuterHexadKernel m22SourceOctad) =
      fixedSpace m22OuterCocodeRepresentation (m22OuterHexadKernel m22SourceOctad) := by
  unfold fixed
  rw [outer_transvection_representation]

/-- The transfer's outer W is literally the native fixed-space span. -/
theorem outer_transvection_span :
    span (MonoidHom.id m22PairStabilizer) (m22OuterHexadKernel m22SourceOctad) =
      fixedSpaceSpan m22OuterCocodeRepresentation (m22OuterHexadKernel m22SourceOctad) := by
  unfold span
  rw [outer_transvection_representation]

/-- The transfer's inner U is literally the fixed space for native M22. -/
theorem inner_transvection_fixed :
    fixed m22ToPairStabilizer (m22InnerHexadKernel m22SourceOctad) =
      fixedSpace m22CocodeRepresentation (m22InnerHexadKernel m22SourceOctad) := by
  unfold fixed
  rw [inner_transvection_representation]

/-- The transfer's inner W is literally the native M22 fixed-space span. -/
theorem inner_transvection_span :
    span m22ToPairStabilizer (m22InnerHexadKernel m22SourceOctad) =
      fixedSpaceSpan m22CocodeRepresentation (m22InnerHexadKernel m22SourceOctad) := by
  unfold span
  rw [inner_transvection_representation]

section Outer

variable (h : RestrictionInput (MonoidHom.id m22PairStabilizer)
  (m22OuterHexadKernel m22SourceOctad) m22SourceOctad)
variable (hd : ∀ z ∈ octadPointwiseKernel m22SourceOctad, z ≠ 1 →
  fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)
variable (ht : AmbientTransvectionInput m22SourceOctad)

/-- The actual iterated quotient for the outer setwise pair group. -/
def outer_transvectionQuotientEquiv :
    (Cocode ⧸ ambientFixed m22SourceOctad) ≃ₗ[ZMod 2]
      (M22Cocode ⧸ fixed (MonoidHom.id m22PairStabilizer)
        (m22OuterHexadKernel m22SourceOctad)) := quotientEquiv h hd

/-- The full group identification, with the literal quotient W/U as target. -/
def outer_transvectionKernelEquiv :
    m22OuterHexadKernel m22SourceOctad ≃* Multiplicative
      ((span (MonoidHom.id m22PairStabilizer) (m22OuterHexadKernel m22SourceOctad)) ⧸
        (fixed (MonoidHom.id m22PairStabilizer) (m22OuterHexadKernel m22SourceOctad)).comap
          (span (MonoidHom.id m22PairStabilizer)
            (m22OuterHexadKernel m22SourceOctad)).subtype) :=
  literalTransvectionEquiv h hd ht

/-- Every prescribed transvection occurs in the outer kernel action, and
there are no other induced linear maps. -/
theorem outer_full_transvection_image
    (T : Module.End (ZMod 2) (M22Cocode ⧸ fixed (MonoidHom.id m22PairStabilizer)
      (m22OuterHexadKernel m22SourceOctad))) :
    (∃ a : m22OuterHexadKernel m22SourceOctad,
      quotientAction h ⟨a.val, kernel_le h a.property⟩ = T) ↔
      ∃ b : axis (MonoidHom.id m22PairStabilizer) (m22OuterHexadKernel m22SourceOctad),
        ∀ x, T x = x + parity h hd ht x • b.val :=
  full_image h hd ht T

/-- The source axis is exactly the kernel of the descended octad parity. -/
theorem outer_transvection_axis :
    (parity h hd ht).ker =
      (span (MonoidHom.id m22PairStabilizer) (m22OuterHexadKernel m22SourceOctad)).map
        (fixed (MonoidHom.id m22PairStabilizer) (m22OuterHexadKernel m22SourceOctad)).mkQ :=
  parity_ker h hd ht

/-- The genuine outer stabilizer/kernel module identification. -/
theorem outer_transvection_conjugation
    (g : m22OuterHexadStabilizer m22SourceOctad)
    (a : m22OuterHexadKernel m22SourceOctad) :
    (transvectionEquiv h hd ht (kernelConj _ _ (normalizes h) g a)).toAdd =
      axisQuotientAction h hd ht (QuotientGroup.mk g) (transvectionEquiv h hd ht a).toAdd :=
  quotient_conjugation h hd ht g a

/-- The ambient and outer axis identifications retain the actual stabilizer map. -/
theorem outer_transvection_axis_equivariant
    (g : m22OuterHexadStabilizer m22SourceOctad) (a : ambientAxis m22SourceOctad) :
    axisEquiv h hd (ambientAxisAction ht (stabilizerMap (f := MonoidHom.id m22PairStabilizer) (O := m22SourceOctad) g) a) =
      axisAction h hd ht g (axisEquiv h hd a) :=
  axisEquiv_equivariant h hd ht g a

end Outer

section Inner

variable (h : RestrictionInput m22ToPairStabilizer
  (m22InnerHexadKernel m22SourceOctad) m22SourceOctad)
variable (hd : ∀ z ∈ octadPointwiseKernel m22SourceOctad, z ≠ 1 →
  fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)
variable (ht : AmbientTransvectionInput m22SourceOctad)

/-- The actual iterated quotient for native M22. -/
def inner_transvectionQuotientEquiv :
    (Cocode ⧸ ambientFixed m22SourceOctad) ≃ₗ[ZMod 2]
      (M22Cocode ⧸ fixed m22ToPairStabilizer
        (m22InnerHexadKernel m22SourceOctad)) := quotientEquiv h hd

/-- The full native M22 kernel identification with the literal quotient W/U. -/
def inner_transvectionKernelEquiv :
    m22InnerHexadKernel m22SourceOctad ≃* Multiplicative
      ((span m22ToPairStabilizer (m22InnerHexadKernel m22SourceOctad)) ⧸
        (fixed m22ToPairStabilizer (m22InnerHexadKernel m22SourceOctad)).comap
          (span m22ToPairStabilizer
            (m22InnerHexadKernel m22SourceOctad)).subtype) :=
  literalTransvectionEquiv h hd ht

/-- Every prescribed transvection occurs in the native M22 kernel action. -/
theorem inner_full_transvection_image
    (T : Module.End (ZMod 2) (M22Cocode ⧸ fixed m22ToPairStabilizer
      (m22InnerHexadKernel m22SourceOctad))) :
    (∃ a : m22InnerHexadKernel m22SourceOctad,
      quotientAction h ⟨a.val, kernel_le h a.property⟩ = T) ↔
      ∃ b : axis m22ToPairStabilizer (m22InnerHexadKernel m22SourceOctad),
        ∀ x, T x = x + parity h hd ht x • b.val :=
  full_image h hd ht T

/-- Native M22 has the same prescribed parity axis after quotienting. -/
theorem inner_transvection_axis :
    (parity h hd ht).ker =
      (span m22ToPairStabilizer (m22InnerHexadKernel m22SourceOctad)).map
        (fixed m22ToPairStabilizer (m22InnerHexadKernel m22SourceOctad)).mkQ :=
  parity_ker h hd ht

/-- The genuine native M22 stabilizer/kernel module identification. -/
theorem inner_transvection_conjugation
    (g : m22InnerHexadStabilizer m22SourceOctad)
    (a : m22InnerHexadKernel m22SourceOctad) :
    (transvectionEquiv h hd ht (kernelConj _ _ (normalizes h) g a)).toAdd =
      axisQuotientAction h hd ht (QuotientGroup.mk g) (transvectionEquiv h hd ht a).toAdd :=
  quotient_conjugation h hd ht g a

/-- The axis identification intertwines the actual native M22 inclusion. -/
theorem inner_transvection_axis_equivariant
    (g : m22InnerHexadStabilizer m22SourceOctad) (a : ambientAxis m22SourceOctad) :
    axisEquiv h hd (ambientAxisAction ht (stabilizerMap (f := m22ToPairStabilizer) (O := m22SourceOctad) g) a) =
      axisAction h hd ht g (axisEquiv h hd a) :=
  axisEquiv_equivariant h hd ht g a

end Inner
end CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad
