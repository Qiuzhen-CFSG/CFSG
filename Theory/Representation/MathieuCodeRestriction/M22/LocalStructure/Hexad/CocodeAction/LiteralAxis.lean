module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.Transvections

/-!
# The literal hexad axis as a stabilizer quotient module

The canonical identification of W/U with its image in V/U transports the
already constructed axis action to the literal subquotient. Its formula on
representatives proves that this is the action induced by the original cocode
representation. The full-transvection parameter identifies the actual kernel
with the additive group of W/U and intertwines stabilizer conjugation.

All normality is relative to the hexad stabilizer. The earlier M24 action and
H.14 displacement remain the precise inputs of the transvection transfer.

Source: Aschbacher--Smith, H.15.2(6), printed pp.398--399,
combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu.M24LocalGeometry
open MathieuCode MathieuCode.Hexad
namespace MathieuCode.Hexad.CocodeAction.Transvections
variable {G : Type*} [Group G]
variable {f : G →* m22PairStabilizer} {K : Subgroup G} {O : Octad}
variable (h : RestrictionInput f K O)
variable (hd : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
  Representation.BinaryOffender.fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)
variable (ht : AmbientTransvectionInput O)

/-- The genuine stabilizer/kernel action on the literal quotient W/U. -/
def literalAxisQuotientAction :
    letI := relativeKernelNormal h
    Representation (ZMod 2) (stabilizer f O ⧸ K.subgroupOf (stabilizer f O))
      ((span f K) ⧸ (fixed f K).comap (span f K).subtype) := by
  letI := relativeKernelNormal h
  exact (spanQuotientEquivAxis (f := f) (K := K)).symm.conjRingEquiv.toMonoidHom.comp
    (axisQuotientAction h hd ht)

/-- The canonical embedding of W/U in V/U intertwines the quotient actions. -/
theorem literalAxisQuotientAction_equivariant
    (q : letI := relativeKernelNormal h; stabilizer f O ⧸ K.subgroupOf (stabilizer f O))
    (w : (span f K) ⧸ (fixed f K).comap (span f K).subtype) :
    spanQuotientEquivAxis (literalAxisQuotientAction h hd ht q w) =
      axisQuotientAction h hd ht q (spanQuotientEquivAxis w) :=
  (spanQuotientEquivAxis (f := f) (K := K)).apply_symm_apply _

/-- The identification with the literal quotient W/U respects stabilizer conjugation. -/
theorem literalTransvectionEquiv_conjugation (g : stabilizer f O) (a : K) :
    (literalTransvectionEquiv h hd ht (kernelConj _ _ (normalizes h) g a)).toAdd =
      literalAxisQuotientAction h hd ht (QuotientGroup.mk g)
        (literalTransvectionEquiv h hd ht a).toAdd := by
  apply (spanQuotientEquivAxis (f := f) (K := K)).injective
  rw [literalAxisQuotientAction_equivariant, literalTransvectionEquiv_axis,
    literalTransvectionEquiv_axis]
  exact quotient_conjugation h hd ht g a

include h hd ht in
/-- W is invariant in the actual cocode, not just after passage to V/U. -/
theorem span_invariant (g : stabilizer f O) {w : M22Cocode} (hw : w ∈ span f K) :
    quotientRepresentation f g.val w ∈ span f K := by
  have hwq : (fixed f K).mkQ w ∈ axis f K := Submodule.mem_map_of_mem hw
  have he := (axisSubrepresentation h hd ht).apply_mem_toSubmodule g hwq
  change (fixed f K).mkQ (quotientRepresentation f g.val w) ∈
    (span f K).map (fixed f K).mkQ at he
  change quotientRepresentation f g.val w ∈
    ((span f K).map (fixed f K).mkQ).comap (fixed f K).mkQ at he
  rw [Submodule.comap_map_eq, Submodule.ker_mkQ,
    sup_eq_left.mpr (fixed_le_span h hd ht)] at he
  exact he

/-- On representatives, the literal quotient action is induced by the original action. -/
theorem literalAxisQuotientAction_mk (g : stabilizer f O) (w : span f K) :
    literalAxisQuotientAction h hd ht (QuotientGroup.mk g)
      (((fixed f K).comap (span f K).subtype).mkQ w) =
    ((fixed f K).comap (span f K).subtype).mkQ
      ⟨quotientRepresentation f g.val w.val, span_invariant h hd ht g w.property⟩ := by
  apply (spanQuotientEquivAxis (f := f) (K := K)).injective
  rw [literalAxisQuotientAction_equivariant]
  apply Subtype.ext
  rfl

/-- The kernel parameter in the shear formula lies in the literal quotient W/U. -/
theorem literal_kernel_action (a : K) (x : M22Cocode ⧸ fixed f K) :
    quotientAction h ⟨a.val, kernel_le h a.property⟩ x = x + parity h hd ht x •
      (spanQuotientEquivAxis (literalTransvectionEquiv h hd ht a).toAdd).val := by
  rw [literalTransvectionEquiv_axis]
  exact kernel_action h hd ht a x

end MathieuCode.Hexad.CocodeAction.Transvections
